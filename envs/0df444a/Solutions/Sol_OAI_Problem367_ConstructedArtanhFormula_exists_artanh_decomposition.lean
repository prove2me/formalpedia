-- Prove2me | solution 1 for OAI.Problem367.ConstructedArtanhFormula.exists_artanh_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:41:25.768881+00:00
-- url     : https://prove2.me/submissions/738431be-03eb-40c7-8cfb-a568ad2e9243

import Mathlib
import Definitions.Def_Q243FI003

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_SimpleIntegralIsometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Problem367.SimpleIntegral

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem integral_mul_eq_zero_of_condExp_eq_zero [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {H D : Ω → ℝ}
    (hH : StronglyMeasurable[m] H) (hD : Integrable D μ)
    (hHD : Integrable (H * D) μ) (hzero : μ[D | m] =ᵐ[μ] 0) :
    ∫ ω, H ω * D ω ∂μ = 0 := by
  have hpull := condExp_mul_of_stronglyMeasurable_left hH hHD hD
  have hCE : μ[H * D | m] =ᵐ[μ] 0 := by
    filter_upwards [hpull, hzero] with ω hp hz
    simp only [Pi.mul_apply, Pi.zero_apply] at hp hz ⊢
    rw [hp, hz, mul_zero]
  calc
    ∫ ω, H ω * D ω ∂μ = ∫ ω, μ[H * D | m] ω ∂μ :=
      (integral_condExp hm).symm
    _ = 0 := by rw [integral_congr_ae hCE]; simp

theorem predictable_increments_orthogonal [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ mΩ) (H D : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[ℱ i] (H i))
    (hD : ∀ i, StronglyMeasurable[ℱ (i + 1)] (D i))
    (hDint : ∀ i, Integrable (D i) μ)
    (hHD : ∀ i, MemLp (fun ω => H i ω * D i ω) 2 μ)
    (hzero : ∀ i, μ[D i | ℱ i] =ᵐ[μ] 0)
    {i j : ℕ} (hij : i < j) :
    ∫ ω, (H i ω * D i ω) * (H j ω * D j ω) ∂μ = 0 := by
  have hcoeff : StronglyMeasurable[ℱ j]
      (fun ω => (H i ω * D i ω) * H j ω) := by
    simpa only [Pi.mul_def] using
      (((hH i).mono (ℱ.mono hij.le)).mul
        ((hD i).mono (ℱ.mono (Nat.succ_le_of_lt hij)))).mul (hH j)
  have hprod : Integrable
      ((fun ω => (H i ω * D i ω) * H j ω) * D j) μ := by
    simpa only [Pi.mul_def, mul_assoc] using (hHD i).integrable_mul (hHD j)
  simpa only [mul_assoc] using
    integral_mul_eq_zero_of_condExp_eq_zero (ℱ.le j) hcoeff (hDint j) hprod (hzero j)

end Problem367.SimpleIntegral

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_GridRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.BrownianGrid

lemma sum_range_blocks {E : Type*} [AddCommMonoid E] (f : ℕ → E) (n k : ℕ) :
    ∑ i ∈ Finset.range (n * k), f i =
      ∑ j ∈ Finset.range n, ∑ l ∈ Finset.range k, f (j * k + l) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

lemma weighted_sum_refinement (x H : ℕ → ℝ) (n : ℕ) {k : ℕ} (hk : 0 < k) :
    (∑ j ∈ Finset.range n, H j * (x ((j + 1) * k) - x (j * k))) =
      ∑ i ∈ Finset.range (n * k), H (i / k) * (x (i + 1) - x i) := by
  rw [sum_range_blocks]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    H j * (x ((j + 1) * k) - x (j * k)) =
        H j * (∑ l ∈ Finset.range k, (x (j * k + (l + 1)) - x (j * k + l))) := by
      rw [Finset.sum_range_sub (fun l => x (j * k + l)) k]
      simp [Nat.add_mul]
    _ = ∑ l ∈ Finset.range k, H j * (x (j * k + (l + 1)) - x (j * k + l)) :=
      Finset.mul_sum _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l hl
      have hdiv : (j * k + l) / k = j := by
        rw [Nat.mul_comm j k, Nat.mul_add_div hk, Nat.div_eq_of_lt (Finset.mem_range.mp hl)]
        omega
      rw [hdiv]
      congr 3

theorem integralSum_refinement {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (H : ℕ → Ω → ℝ) (n : ℕ) {k : ℕ} (hk : 0 < k) :
    integralSum B (fun j => t (j * k)) H n =
      integralSum B t (fun i => H (i / k)) (n * k) := by
  funext ω
  exact weighted_sum_refinement (fun i => B (t i) ω) (fun i => H i ω) n hk

end Problem367.BrownianGrid

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_UniformGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.BrownianGrid

lemma uniformGrid_refine (T : ℝ≥0) {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (j : ℕ) : uniformGrid T (n * k) (j * k) = uniformGrid T n j := by
  have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hk0 : (k : ℝ≥0) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  simp only [uniformGrid, Nat.cast_mul]
  field_simp

lemma uniformGrid_le_horizon (T : ℝ≥0) {n i : ℕ} (hn : 0 < n) (hi : i ≤ n) :
    uniformGrid T n i ≤ T := by
  simpa only [uniformGrid_end T hn] using uniformGrid_mono T n hi

lemma uniformGrid_floor_le (T : ℝ≥0) {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (i : ℕ) : uniformGrid T n (i / k) ≤ uniformGrid T (n * k) i := by
  rw [← uniformGrid_refine T hn hk]
  exact uniformGrid_mono T (n * k) (Nat.div_mul_le_self i k)

lemma uniformGrid_floor_sub_le (T : ℝ≥0) {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (i : ℕ) :
    (uniformGrid T (n * k) i : ℝ) - (uniformGrid T n (i / k) : ℝ) ≤
      (T : ℝ) / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hindex : i ≤ (i / k) * k + k := by
    have hmod := Nat.mod_lt i hk
    have hdecomp := Nat.mod_add_div i k
    rw [Nat.mul_comm k (i / k)] at hdecomp
    omega
  have hiR : (i : ℝ) ≤ (i / k : ℕ) * (k : ℝ) + (k : ℝ) := by exact_mod_cast hindex
  simp only [uniformGrid, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast, Nat.cast_mul]
  apply (sub_le_iff_le_add).2
  apply (div_le_iff₀ (mul_pos hnR hkR)).2
  field_simp
  nlinarith [mul_le_mul_of_nonneg_right hiR T.coe_nonneg]

lemma integral_sq_sub_le_two {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y Z : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P) (hZ : MemLp Z 2 P) :
    (∫ ω, (X ω - Y ω) ^ 2 ∂P) ≤
      2 * (∫ ω, (X ω - Z ω) ^ 2 ∂P) + 2 * (∫ ω, (Y ω - Z ω) ^ 2 ∂P) := by
  have hXY : Integrable (fun ω => (X ω - Y ω) ^ 2) P := (hX.sub hY).integrable_sq
  have hXZ : Integrable (fun ω => (X ω - Z ω) ^ 2) P := (hX.sub hZ).integrable_sq
  have hYZ : Integrable (fun ω => (Y ω - Z ω) ^ 2) P := (hY.sub hZ).integrable_sq
  calc
    _ ≤ ∫ ω, 2 * (X ω - Z ω) ^ 2 + 2 * (Y ω - Z ω) ^ 2 ∂P := by
      apply integral_mono hXY ((hXZ.const_mul 2).add (hYZ.const_mul 2))
      intro ω
      change (X ω - Y ω) ^ 2 ≤ 2 * (X ω - Z ω) ^ 2 + 2 * (Y ω - Z ω) ^ 2
      nlinarith [sq_nonneg (X ω + Y ω - 2 * Z ω)]
    _ = _ := by
      rw [integral_add (hXZ.const_mul 2) (hYZ.const_mul 2), integral_const_mul, integral_const_mul]

end Problem367.BrownianGrid

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_UniformIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianGrid

lemma norm_sq_L2_eq_integral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (f : Lp ℝ 2 P) : ‖f‖ ^ 2 = ∫ ω, (f ω) ^ 2 ∂P := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

lemma norm_sq_toLp_sub {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ ω, (f ω - g ω) ^ 2 ∂P := by
  rw [norm_sq_L2_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp]
    with ω hsub hfw hgw
  simp only [Pi.sub_apply] at hsub
  rw [hsub, hfw, hgw]

end Problem367.BrownianGrid

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_EnergyRiemannApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators

namespace Problem367.EnergyRiemann

theorem point_end (T : ℝ) {n : ℕ} (hn : 0 < n) : point T n n = T := by
  dsimp [point]
  field_simp

theorem point_step (T : ℝ) (n i : ℕ) :
    point T n (i + 1) - point T n i = T / n := by
  simp only [point, Nat.cast_add, Nat.cast_one]
  ring

theorem point_mono {T : ℝ} (hT : 0 ≤ T) (n : ℕ) : Monotone (point T n) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity)

theorem point_mem {T : ℝ} (hT : 0 ≤ T) {n i : ℕ} (hn : 0 < n) (hi : i ≤ n) :
    point T n i ∈ Icc 0 T := by
  constructor
  · dsimp [point] <;> positivity
  · exact (point_mono hT n hi).trans_eq (point_end T hn)

end Problem367.EnergyRiemann

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ArtanhTaylor
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace Problem367.ArtanhTaylor

lemma denominator_pos {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    0 < 1 - x ^ 2 := by
  nlinarith [hx.1, hx.2]

theorem contDiffAt_artanh {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1)
    (n : WithTop ENat) : ContDiffAt ℝ n Real.artanh x := by
  have hm : 0 < 1 - x := by linarith [hx.2]
  have hp : 0 < 1 + x := by linarith [hx.1]
  have hq : 0 < (1 + x) / (1 - x) := div_pos hp hm
  unfold Real.artanh
  exact (((contDiffAt_const.add contDiffAt_id).div
    (contDiffAt_const.sub contDiffAt_id) hm.ne').sqrt hq.ne').log
      (Real.sqrt_pos.mpr hq).ne'

lemma hasDerivAt_first {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y : ℝ => 1 / (1 - y ^ 2))
      (2 * x / (1 - x ^ 2) ^ 2) x := by
  have h := (hasDerivAt_const x (1 : ℝ)).div
    (((hasDerivAt_id x).pow 2).const_sub 1) (denominator_pos hx).ne'
  apply h.congr_deriv
  dsimp
  ring

lemma hasDerivAt_second {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y : ℝ => 2 * y / (1 - y ^ 2) ^ 2)
      ((2 + 6 * x ^ 2) / (1 - x ^ 2) ^ 3) x := by
  have h := ((hasDerivAt_id x).const_mul 2).div
    ((((hasDerivAt_id x).pow 2).const_sub 1).pow 2)
    (pow_ne_zero 2 (denominator_pos hx).ne')
  apply h.congr_deriv
  dsimp
  field_simp [(denominator_pos hx).ne']
  ring

lemma iteratedDeriv_two {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    iteratedDeriv 2 Real.artanh x = 2 * x / (1 - x ^ 2) ^ 2 := by
  have he : deriv Real.artanh =ᶠ[𝓝 x] (fun y : ℝ => 1 / (1 - y ^ 2)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact (hasDerivAt_artanh_interval hy).deriv
  rw [show 2 = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  exact he.deriv_eq.trans (hasDerivAt_first hx).deriv

lemma iteratedDeriv_three {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    iteratedDeriv 3 Real.artanh x = (2 + 6 * x ^ 2) / (1 - x ^ 2) ^ 3 := by
  have he : iteratedDeriv 2 Real.artanh =ᶠ[𝓝 x]
      (fun y : ℝ => 2 * y / (1 - y ^ 2) ^ 2) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact iteratedDeriv_two hy
  rw [show 3 = 2 + 1 from rfl, iteratedDeriv_succ]
  exact he.deriv_eq.trans (hasDerivAt_second hx).deriv

theorem abs_iteratedDeriv_three_le {r x : ℝ} (hr : r < 1)
    (hx : |x| ≤ r) :
    |iteratedDeriv 3 Real.artanh x| ≤ 8 / (1 - r ^ 2) ^ 3 := by
  have hr0 : 0 ≤ r := (abs_nonneg x).trans hx
  have hx1 : |x| < 1 := hx.trans_lt hr
  have hmem : x ∈ Ioo (-1 : ℝ) 1 := abs_lt.mp hx1
  have hsq : x ^ 2 ≤ r ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg x) hr0).2 hx
  have hrden : 0 < 1 - r ^ 2 := by nlinarith
  have hxden := denominator_pos hmem
  rw [iteratedDeriv_three hmem, abs_of_nonneg (by positivity)]
  calc
    (2 + 6 * x ^ 2) / (1 - x ^ 2) ^ 3 ≤ 8 / (1 - x ^ 2) ^ 3 := by
      gcongr
      nlinarith
    _ ≤ 8 / (1 - r ^ 2) ^ 3 := by
      gcongr

theorem abs_remainder_le {r x y : ℝ} (hr : r < 1)
    (hx : |x| ≤ r) (hy : |y| ≤ r) :
    |Real.artanh y - Real.artanh x - (y - x) / (1 - x ^ 2) -
      x * (y - x) ^ 2 / (1 - x ^ 2) ^ 2| ≤
        (8 / (1 - r ^ 2) ^ 3) * |y - x| ^ 3 := by
  by_cases hxy : x = y
  · subst y
    simp
  have hr0 : 0 ≤ r := (abs_nonneg x).trans hx
  have hrden : 0 < 1 - r ^ 2 := by nlinarith
  have hseg : uIcc x y ⊆ Icc (-r) r := uIcc_subset_Icc (abs_le.mp hx) (abs_le.mp hy)
  have hmem (z : ℝ) (hz : z ∈ uIcc x y) : z ∈ Ioo (-1 : ℝ) 1 := by
    have hh := hseg hz
    constructor <;> linarith [hh.1, hh.2]
  have hsmooth : ContDiffOn ℝ (3 : ℕ) Real.artanh (uIcc x y) :=
    fun z hz => (contDiffAt_artanh (hmem z hz) 3).contDiffWithinAt
  obtain ⟨z, hz, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 2) hxy hsmooth
  have hu : UniqueDiffOn ℝ (uIcc x y) := uniqueDiffOn_Icc (by grind)
  have hxm := hmem x (left_mem_uIcc)
  have hw (k : ℕ) : iteratedDerivWithin k Real.artanh (uIcc x y) x =
      iteratedDeriv k Real.artanh x :=
    iteratedDerivWithin_eq_iteratedDeriv hu (contDiffAt_artanh hxm k) left_mem_uIcc
  have hp : taylorWithinEval Real.artanh 2 (uIcc x y) x y =
      Real.artanh x + (y - x) / (1 - x ^ 2) +
        x * (y - x) ^ 2 / (1 - x ^ 2) ^ 2 := by
    simp only [taylorWithinEval_succ, taylor_within_zero_eval, hw, iteratedDeriv_two hxm]
    norm_num
    rw [(hasDerivAt_artanh_interval hxm).deriv]
    ring
  have hzabs : |z| ≤ r := abs_le.mpr (hseg ⟨hz.1.le, hz.2.le⟩)
  have hC : 0 ≤ 8 / (1 - r ^ 2) ^ 3 := by positivity
  have hbound := abs_iteratedDeriv_three_le hr hzabs
  rw [hp] at heq
  norm_num at heq
  calc
    |Real.artanh y - Real.artanh x - (y - x) / (1 - x ^ 2) -
        x * (y - x) ^ 2 / (1 - x ^ 2) ^ 2| =
        |iteratedDeriv 3 Real.artanh z| * |y - x| ^ 3 / 6 := by
      have heq' : Real.artanh y - Real.artanh x - (y - x) / (1 - x ^ 2) -
          x * (y - x) ^ 2 / (1 - x ^ 2) ^ 2 =
          iteratedDeriv 3 Real.artanh z * (y - x) ^ 3 / 6 := by
        linarith [heq]
      rw [heq', abs_div, abs_mul, abs_pow]
      norm_num
    _ ≤ (8 / (1 - r ^ 2) ^ 3) * |y - x| ^ 3 / 6 := by gcongr
    _ ≤ (8 / (1 - r ^ 2) ^ 3) * |y - x| ^ 3 := by
      nlinarith [mul_nonneg hC (pow_nonneg (abs_nonneg (y - x)) 3)]

theorem sum_remainder (x : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, remainder (x i) (x (i + 1))) =
      Real.artanh (x n) - Real.artanh (x 0) -
        (∑ i ∈ Finset.range n, (x (i + 1) - x i) / (1 - (x i) ^ 2)) -
        ∑ i ∈ Finset.range n,
          x i * (x (i + 1) - x i) ^ 2 / (1 - (x i) ^ 2) ^ 2 := by
  calc
    _ = (∑ i ∈ Finset.range n, (Real.artanh (x (i + 1)) - Real.artanh (x i))) -
        (∑ i ∈ Finset.range n, (x (i + 1) - x i) / (1 - (x i) ^ 2)) -
        ∑ i ∈ Finset.range n,
          x i * (x (i + 1) - x i) ^ 2 / (1 - (x i) ^ 2) ^ 2 := by
      simp only [remainder, Finset.sum_sub_distrib]
    _ = _ := by rw [Finset.sum_range_sub (fun i => Real.artanh (x i)) n]

section Probability

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma measurable_remainder {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) :
    Measurable (fun ω => remainder (X ω) (Y ω)) := by
  unfold remainder Real.artanh
  fun_prop

theorem integrable_sum_remainder_and_bound {r : ℝ} (hr : r < 1)
    (x : ℕ → Ω → ℝ) (n : ℕ) (hm : ∀ i, Measurable (x i))
    (hx : ∀ᵐ ω ∂μ, ∀ i ≤ n, |x i ω| ≤ r)
    (hcube : ∀ i < n, Integrable (fun ω => |x (i + 1) ω - x i ω| ^ 3) μ) :
    Integrable (fun ω => ∑ i ∈ Finset.range n, remainder (x i ω) (x (i + 1) ω)) μ ∧
      (∫ ω, |∑ i ∈ Finset.range n, remainder (x i ω) (x (i + 1) ω)| ∂μ) ≤
        (8 / (1 - r ^ 2) ^ 3) *
          ∑ i ∈ Finset.range n, ∫ ω, |x (i + 1) ω - x i ω| ^ 3 ∂μ := by
  have hdom : Integrable (fun ω => (8 / (1 - r ^ 2) ^ 3) *
      ∑ i ∈ Finset.range n, |x (i + 1) ω - x i ω| ^ 3) μ :=
    (integrable_finsetSum _ (fun i hi => hcube i (Finset.mem_range.mp hi))).const_mul _
  have hrm : Measurable (fun ω => ∑ i ∈ Finset.range n,
      remainder (x i ω) (x (i + 1) ω)) :=
    Finset.measurable_fun_sum _ (fun i _ => measurable_remainder (hm i) (hm (i + 1)))
  have hb : ∀ᵐ ω ∂μ, |∑ i ∈ Finset.range n, remainder (x i ω) (x (i + 1) ω)| ≤
      (8 / (1 - r ^ 2) ^ 3) * ∑ i ∈ Finset.range n, |x (i + 1) ω - x i ω| ^ 3 := by
    filter_upwards [hx] with ω hω
    calc
      _ ≤ ∑ i ∈ Finset.range n, |remainder (x i ω) (x (i + 1) ω)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range n,
          (8 / (1 - r ^ 2) ^ 3) * |x (i + 1) ω - x i ω| ^ 3 := by
        apply Finset.sum_le_sum
        intro i hi
        have hin := Finset.mem_range.mp hi
        exact abs_remainder_le hr (hω i hin.le) (hω (i + 1) hin)
      _ = _ := by rw [Finset.mul_sum]
  have hi : Integrable (fun ω => ∑ i ∈ Finset.range n,
      remainder (x i ω) (x (i + 1) ω)) μ := by
    apply hdom.mono' hrm.aestronglyMeasurable
    simpa only [Real.norm_eq_abs] using hb
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ ω, (8 / (1 - r ^ 2) ^ 3) *
        ∑ i ∈ Finset.range n, |x (i + 1) ω - x i ω| ^ 3 ∂μ :=
      integral_mono_ae hi.abs hdom hb
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _
        (fun i hi => hcube i (Finset.mem_range.mp hi))]

theorem integrable_cube_of_localized [IsFiniteMeasure μ]
    {r : ℝ} {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hx : ∀ᵐ ω ∂μ, |X ω| ≤ r) (hy : ∀ᵐ ω ∂μ, |Y ω| ≤ r) :
    Integrable (fun ω => |Y ω - X ω| ^ 3) μ := by
  apply Integrable.of_bound ((hY.sub hX).abs.pow_const 3).aestronglyMeasurable ((2 * r) ^ 3)
  filter_upwards [hx, hy] with ω hxω hyω
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) 3)]
  have hd : |Y ω - X ω| ≤ 2 * r := by
    calc
      _ ≤ |Y ω| + |X ω| := abs_sub _ _
      _ ≤ _ := by linarith
  exact pow_le_pow_left₀ (abs_nonneg _) hd 3

theorem tendsto_integral_abs_sum_remainder [IsFiniteMeasure μ]
    {r : ℝ} (hr : r < 1) (x : ℕ → ℕ → Ω → ℝ) (N : ℕ → ℕ)
    (hm : ∀ k i, Measurable (x k i))
    (hx : ∀ k, ∀ᵐ ω ∂μ, ∀ i ≤ N k, |x k i ω| ≤ r)
    (hthird : Tendsto (fun k => ∑ i ∈ Finset.range (N k),
      ∫ ω, |x k (i + 1) ω - x k i ω| ^ 3 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω,
      |∑ i ∈ Finset.range (N k), remainder (x k i ω) (x k (i + 1) ω)| ∂μ)
      atTop (𝓝 0) := by
  have hb (k : ℕ) := integrable_sum_remainder_and_bound hr (x k) (N k) (hm k) (hx k)
    (fun i hi => integrable_cube_of_localized (hm k i) (hm k (i + 1))
      ((hx k).mono fun ω hω => hω i hi.le)
      ((hx k).mono fun ω hω => hω (i + 1) hi))
  apply squeeze_zero (fun k => integral_nonneg (fun ω => abs_nonneg _)) (fun k => (hb k).2)
  simpa only [mul_zero] using hthird.const_mul (8 / (1 - r ^ 2) ^ 3)

end Probability

end Problem367.ArtanhTaylor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_WeightedPrimitiveApproximation
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace Problem367.WeightedPrimitiveApproximation

open EnergyRiemann (point point_zero point_end point_step point_mono point_mem)

lemma cell_subset {T : ℝ} (hT : 0 ≤ T) {n i : ℕ}
    (hn : 0 < n) (hi : i < n) :
    uIcc (point T n i) (point T n (i + 1)) ⊆ uIcc (0 : ℝ) T := by
  rw [uIcc_of_le hT]
  exact uIcc_subset_Icc (point_mem hT hn hi.le) (point_mem hT hn hi)

theorem error_le {f a : ℝ → ℝ} {T ε : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc 0 T)) (ha : IntervalIntegrable a volume 0 T)
    {n : ℕ} (hn : 0 < n)
    (hmod : ∀ i < n, ∀ s ∈ Icc (point T n i) (point T n (i + 1)),
      |f (point T n i) - f s| ≤ ε) :
    |weightedSum f a T n - ∫ s in (0 : ℝ)..T, f s * a s| ≤
      ε * ∫ s in (0 : ℝ)..T, |a s| := by
  have hfa : IntervalIntegrable (fun s => f s * a s) volume 0 T := by
    simpa only [mul_comm, uIcc_of_le hT] using ha.mul_continuousOn
      (show ContinuousOn f (uIcc 0 T) by simpa only [uIcc_of_le hT] using hf)
  have hcellA (i : ℕ) (hi : i < n) := ha.mono_set (cell_subset hT hn hi)
  have hcellFA (i : ℕ) (hi : i < n) := hfa.mono_set (cell_subset hT hn hi)
  have hpart := intervalIntegral.sum_integral_adjacent_intervals hcellFA
  rw [point_zero, point_end T hn] at hpart
  have hpartAbs := intervalIntegral.sum_integral_adjacent_intervals
    (fun i hi => (hcellA i hi).abs)
  rw [point_zero, point_end T hn] at hpartAbs
  have hdecomp : weightedSum f a T n - (∫ s in (0 : ℝ)..T, f s * a s) =
      ∑ i ∈ Finset.range n, ∫ s in point T n i..point T n (i + 1),
        (f (point T n i) - f s) * a s := by
    rw [weightedSum, ← hpart, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show (fun s => (f (point T n i) - f s) * a s) =
        (fun s => f (point T n i) * a s - f s * a s) by funext s; ring]
    rw [intervalIntegral.integral_sub ((hcellA i (Finset.mem_range.mp hi)).const_mul _)
      (hcellFA i (Finset.mem_range.mp hi)), intervalIntegral.integral_const_mul]
  rw [hdecomp]
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        |∫ s in point T n i..point T n (i + 1), (f (point T n i) - f s) * a s| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n,
        ε * ∫ s in point T n i..point T n (i + 1), |a s| := by
      apply Finset.sum_le_sum
      intro i hi
      have hin := Finset.mem_range.mp hi
      have hle := point_mono hT n (Nat.le_succ i)
      have hdiff : IntervalIntegrable
          (fun s => (f (point T n i) - f s) * a s) volume
          (point T n i) (point T n (i + 1)) := by
        simpa only [sub_mul] using
          ((hcellA i hin).const_mul (f (point T n i))).sub (hcellFA i hin)
      calc
        _ ≤ ∫ s in point T n i..point T n (i + 1),
            |(f (point T n i) - f s) * a s| := by
          simpa only [Real.norm_eq_abs] using
            (intervalIntegral.norm_integral_le_integral_norm (f := fun s =>
              (f (point T n i) - f s) * a s) hle)
        _ ≤ ∫ s in point T n i..point T n (i + 1), ε * |a s| := by
          apply intervalIntegral.integral_mono_on hle hdiff.abs ((hcellA i hin).abs.const_mul ε)
          intro s hs
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hmod i hin s hs) (abs_nonneg _)
        _ = _ := intervalIntegral.integral_const_mul _ _
    _ = _ := by rw [← Finset.mul_sum, hpartAbs]

theorem tendsto_weightedSum {f a : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc 0 T)) (ha : IntervalIntegrable a volume 0 T) :
    Tendsto (weightedSum f a T) atTop (𝓝 (∫ s in (0 : ℝ)..T, f s * a s)) := by
  have hmass : 0 ≤ ∫ s in (0 : ℝ)..T, |a s| :=
    intervalIntegral.integral_nonneg hT (fun _ _ => abs_nonneg _)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε / ((∫ s in (0 : ℝ)..T, |a s|) + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  have hUC := isCompact_Icc.uniformContinuousOn_of_continuous hf
  obtain ⟨δ, hδ, hδmod⟩ := Metric.uniformContinuousOn_iff.mp hUC η hη
  have hwidth : Tendsto (fun n : ℕ => T / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := ((hwidth.eventually (gt_mem_nhds hδ)).and
    (eventually_ge_atTop 1)).exists_forall_of_atTop
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨hmesh, hnpos⟩ := hN n hn
  have hn' : 0 < n := hnpos
  have he := error_le hT hf ha hn' (ε := η) ?_
  · change |weightedSum f a T n - ∫ s in (0 : ℝ)..T, f s * a s| < ε
    apply he.trans_lt
    change ε / ((∫ s in (0 : ℝ)..T, |a s|) + 1) *
      (∫ s in (0 : ℝ)..T, |a s|) < ε
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by linarith : 0 < (∫ s in (0 : ℝ)..T, |a s|) + 1)).mpr
    nlinarith
  · intro i hi s hs
    have hleft := point_mem hT hn' hi.le
    have hright := point_mem hT hn' hi
    have hsT : s ∈ Icc (0 : ℝ) T := ⟨hleft.1.trans hs.1, hs.2.trans hright.2⟩
    have hd : dist (point T n i) s < δ := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hs.1)]
      have hstep := point_step T n i
      linarith [hs.2]
    exact (hδmod _ hleft s hsT hd).le

theorem weightedSum_eq_primitiveSum {f a : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (ha : IntervalIntegrable a volume 0 T) {n : ℕ} (hn : 0 < n) :
    weightedSum f a T n = ∑ i ∈ Finset.range n, f (point T n i) *
      ((∫ s in (0 : ℝ)..point T n (i + 1), a s) -
        ∫ s in (0 : ℝ)..point T n i, a s) := by
  apply Finset.sum_congr rfl
  intro i hi
  have hin := Finset.mem_range.mp hi
  have h0i : IntervalIntegrable a volume 0 (point T n i) := by
    apply ha.mono_set
    rw [uIcc_of_le hT]
    exact uIcc_subset_Icc ⟨le_rfl, hT⟩ (point_mem hT hn hin.le)
  have hcell := ha.mono_set (cell_subset hT hn hin)
  have hadd := intervalIntegral.integral_add_adjacent_intervals h0i hcell
  congr 1
  linarith [hadd]

lemma abs_integral_mul_le {f a : ℝ → ℝ} {T K : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc 0 T)) (ha : IntervalIntegrable a volume 0 T)
    (hb : ∀ s ∈ Icc 0 T, |f s| ≤ K) :
    |∫ s in (0 : ℝ)..T, f s * a s| ≤ K * ∫ s in (0 : ℝ)..T, |a s| := by
  have hfa : IntervalIntegrable (fun s => f s * a s) volume 0 T := by
    simpa only [mul_comm] using ha.mul_continuousOn
      (show ContinuousOn f (uIcc 0 T) by simpa only [uIcc_of_le hT] using hf)
  calc
    _ ≤ ∫ s in (0 : ℝ)..T, |f s * a s| := by
      simpa only [Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_integral_norm (f := fun s => f s * a s) hT)
    _ ≤ ∫ s in (0 : ℝ)..T, K * |a s| := by
      apply intervalIntegral.integral_mono_on hT hfa.abs (ha.abs.const_mul K)
      intro s hs
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hb s hs) (abs_nonneg _)
    _ = _ := intervalIntegral.integral_const_mul _ _

theorem error_le_two_mul_mass {f a : ℝ → ℝ} {T K : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc 0 T)) (ha : IntervalIntegrable a volume 0 T)
    (hK : 0 ≤ K) (hb : ∀ s ∈ Icc 0 T, |f s| ≤ K) (n : ℕ) :
    |weightedSum f a T n - ∫ s in (0 : ℝ)..T, f s * a s| ≤
      (2 * K) * ∫ s in (0 : ℝ)..T, |a s| := by
  by_cases hn : n = 0
  · subst n
    simp only [weightedSum, Finset.range_zero, Finset.sum_empty, zero_sub, abs_neg]
    have hmass : 0 ≤ ∫ s in (0 : ℝ)..T, |a s| :=
      intervalIntegral.integral_nonneg hT (fun _ _ => abs_nonneg _)
    exact (abs_integral_mul_le hT hf ha hb).trans
      (mul_le_mul_of_nonneg_right (by linarith : K ≤ 2 * K) hmass)
  · have hn' := Nat.pos_of_ne_zero hn
    apply error_le hT hf ha hn'
    intro i hi s hs
    have hl := point_mem hT hn' hi.le
    have hr := point_mem hT hn' hi
    have hsT : s ∈ Icc (0 : ℝ) T := ⟨hl.1.trans hs.1, hs.2.trans hr.2⟩
    exact (abs_sub _ _).trans (by linarith [hb _ hl, hb s hsT])

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]

theorem integrable_weightedDensity {T K : ℝ} {f a : ℝ → Ω → ℝ}
    (hfm : Measurable (fun p : ℝ × Ω => f p.1 p.2))
    (ha : Integrable (fun p : ℝ × Ω => a p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hb : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, |f t ω| ≤ K) :
    Integrable (fun p : ℝ × Ω => f p.1 p.2 * a p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ) := by
  have hbp : ∀ᵐ p ∂(volume.restrict (Ioc 0 T)).prod μ, |f p.1 p.2| ≤ K := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hfm.abs measurable_const)).2
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hb.mono fun ω hω => hω t ⟨ht.1.le, ht.2⟩
  apply (ha.norm.const_mul K).mono' (hfm.aestronglyMeasurable.mul ha.aestronglyMeasurable)
  filter_upwards [hbp] with p hp
  simpa only [Real.norm_eq_abs, abs_mul, Pi.mul_apply] using
    mul_le_mul_of_nonneg_right hp (abs_nonneg (a p.1 p.2))

lemma integrable_cellIntegral {T : ℝ} (hT : 0 ≤ T) {a : ℝ → Ω → ℝ}
    (ha : Integrable (fun p : ℝ × Ω => a p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    {n i : ℕ} (hn : 0 < n) (hi : i < n) :
    Integrable (fun ω => ∫ s in point T n i..point T n (i + 1), a s ω) μ := by
  have hl := point_mem hT hn hi.le
  have hr := point_mem hT hn hi
  have hsub : Ioc (point T n i) (point T n (i + 1)) ⊆ Ioc (0 : ℝ) T := by
    intro s hs
    exact ⟨hl.1.trans_lt hs.1, hs.2.trans hr.2⟩
  have hc := ha.mono_measure (Measure.prod_mono
    (Measure.restrict_mono_set _ hsub) le_rfl)
  simpa only [intervalIntegral.integral_of_le (point_mono hT n (Nat.le_succ i))] using
    hc.integral_prod_right

theorem tendsto_integral_abs_error {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
    {f a : ℝ → Ω → ℝ}
    (hfm : Measurable (fun p : ℝ × Ω => f p.1 p.2))
    (hf : ∀ᵐ ω ∂μ, ContinuousOn (fun t => f t ω) (Icc 0 T))
    (ha : Integrable (fun p : ℝ × Ω => a p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hb : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, |f t ω| ≤ K) :
    Tendsto (fun n => ∫ ω, |weightedSum (fun t => f t ω) (fun t => a t ω) T n -
      ∫ t in (0 : ℝ)..T, f t ω * a t ω| ∂μ) atTop (𝓝 0) := by
  have hPath : ∀ᵐ ω ∂μ, IntervalIntegrable (fun t => a t ω) volume 0 T :=
    ha.prod_left_ae.mono fun ω hω => (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 hω
  have hmass : Integrable (fun ω => ∫ t in (0 : ℝ)..T, |a t ω|) μ := by
    simpa only [intervalIntegral.integral_of_le hT] using ha.abs.integral_prod_right
  have htarget : Integrable (fun ω => ∫ t in (0 : ℝ)..T, f t ω * a t ω) μ := by
    simpa only [intervalIntegral.integral_of_le hT] using
      (integrable_weightedDensity hfm ha hb).integral_prod_right
  have hsum (n : ℕ) : AEStronglyMeasurable
      (fun ω => weightedSum (fun t => f t ω) (fun t => a t ω) T n) μ := by
    unfold weightedSum
    apply Finset.aestronglyMeasurable_fun_sum
    intro i hi
    have hin := Finset.mem_range.mp hi
    have hn : 0 < n := (Nat.zero_le i).trans_lt hin
    exact ((hfm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mul
      (integrable_cellIntegral hT ha hn hin).aestronglyMeasurable
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := μ) (F := fun n ω => |weightedSum (fun t => f t ω) (fun t => a t ω) T n -
      ∫ t in (0 : ℝ)..T, f t ω * a t ω|) (f := fun _ => (0 : ℝ))
    (fun ω => (2 * K) * ∫ t in (0 : ℝ)..T, |a t ω|)
    (fun n => by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using
        ((hsum n).sub htarget.aestronglyMeasurable).norm)
    (hmass.const_mul (2 * K)) ?_ ?_
  · simpa only [integral_zero] using hlim
  · intro n
    filter_upwards [hf, hPath, hb] with ω hfω haω hbω
    simpa only [Real.norm_eq_abs, abs_abs] using error_le_two_mul_mass hT hfω haω hK hbω n
  · filter_upwards [hf, hPath] with ω hfω haω
    simpa only [sub_self, abs_zero] using
      ((tendsto_weightedSum hT hfω haω).sub
        (tendsto_const_nhds (x := ∫ t in (0 : ℝ)..T, f t ω * a t ω))).abs

theorem tendsto_integral_abs_compensator_error {T K : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) {f a A : ℝ → Ω → ℝ}
    (hfm : Measurable (fun p : ℝ × Ω => f p.1 p.2))
    (hf : ∀ᵐ ω ∂μ, ContinuousOn (fun t => f t ω) (Icc 0 T))
    (ha : Integrable (fun p : ℝ × Ω => a p.1 p.2)
      ((volume.restrict (Ioc 0 T)).prod μ))
    (hb : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, |f t ω| ≤ K)
    (hA : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      A t ω = A 0 ω + ∫ s in (0 : ℝ)..t, a s ω) :
    Tendsto (fun n => ∫ ω,
      |(∑ i ∈ Finset.range n, f (point T n i) ω *
        (A (point T n (i + 1)) ω - A (point T n i) ω)) -
        ∫ t in (0 : ℝ)..T, f t ω * a t ω| ∂μ) atTop (𝓝 0) := by
  apply (tendsto_integral_abs_error hT hK hfm hf ha hb).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  apply integral_congr_ae
  filter_upwards [ha.prod_left_ae, hA] with ω haω hAω
  have hp := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 haω
  rw [weightedSum_eq_primitiveSum hT hp hn]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  have hin := Finset.mem_range.mp hi
  rw [hAω _ (point_mem hT hn hin), hAω _ (point_mem hT hn hin.le)]
  ring

end Probability

end Problem367.WeightedPrimitiveApproximation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_TaylorRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Problem367.MartingaleTaylorRemainder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem cubic_le_quadratic_add_quartic (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    |x| ^ 3 ≤ ε * x ^ 2 + (1 / (4 * ε)) * x ^ 4 := by
  have hpos : 0 < 4 * ε := mul_pos (by norm_num) hε
  have hid : (4 * ε) *
      (ε * x ^ 2 + (1 / (4 * ε)) * x ^ 4 - |x| ^ 3) =
      (x ^ 2 - 2 * ε * |x|) ^ 2 := by
    have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    have hx4 : x ^ 4 = |x| ^ 4 := by nlinarith [sq_nonneg (x ^ 2 - |x| ^ 2)]
    rw [hx2, hx4]
    field_simp
    ring
  have hnon : 0 ≤ ε * x ^ 2 + (1 / (4 * ε)) * x ^ 4 - |x| ^ 3 := by
    apply (mul_nonneg_iff_of_pos_left hpos).1
    rw [hid]
    exact sq_nonneg _
  linarith

theorem integrable_abs_cube {D : Ω → ℝ}
    (hD : AEStronglyMeasurable D μ)
    (h2 : Integrable (fun ω => D ω ^ 2) μ)
    (h4 : Integrable (fun ω => D ω ^ 4) μ) :
    Integrable (fun ω => |D ω| ^ 3) μ := by
  apply (h2.add (h4.const_mul (1 / 4 : ℝ))).mono' (hD.norm.pow 3)
  filter_upwards [] with ω
  change abs (|D ω| ^ 3) ≤ D ω ^ 2 + (1 / 4 : ℝ) * D ω ^ 4
  simpa only [abs_of_nonneg (pow_nonneg (abs_nonneg (D ω)) 3),
    one_mul, mul_one] using cubic_le_quadratic_add_quartic (D ω) (by norm_num : (0 : ℝ) < 1)

theorem integral_sum_abs_cube_le {ι : Type*} (s : Finset ι) (D : ι → Ω → ℝ)
    (hD : ∀ i ∈ s, AEStronglyMeasurable (D i) μ)
    (h2 : ∀ i ∈ s, Integrable (fun ω => D i ω ^ 2) μ)
    (h4 : ∀ i ∈ s, Integrable (fun ω => D i ω ^ 4) μ)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ ω, ∑ i ∈ s, |D i ω| ^ 3 ∂μ) ≤
      ε * (∫ ω, ∑ i ∈ s, D i ω ^ 2 ∂μ) +
        (1 / (4 * ε)) * (∫ ω, ∑ i ∈ s, D i ω ^ 4 ∂μ) := by
  have hc := integrable_finsetSum s (fun i hi => integrable_abs_cube (hD i hi) (h2 i hi) (h4 i hi))
  have hq := integrable_finsetSum s h2
  have hf := integrable_finsetSum s h4
  calc
    (∫ ω, ∑ i ∈ s, |D i ω| ^ 3 ∂μ) ≤
        ∫ ω, ε * (∑ i ∈ s, D i ω ^ 2) +
          (1 / (4 * ε)) * (∑ i ∈ s, D i ω ^ 4) ∂μ := by
      apply integral_mono hc ((hq.const_mul ε).add (hf.const_mul _))
      intro ω
      simpa only [Pi.add_apply, Finset.sum_add_distrib, Finset.mul_sum] using
        Finset.sum_le_sum (fun i (_ : i ∈ s) => cubic_le_quadratic_add_quartic (D i ω) hε)
    _ = _ := by rw [integral_add (hq.const_mul ε) (hf.const_mul _),
      integral_const_mul, integral_const_mul]

theorem tendsto_zero_of_young_bound {R C : ℕ → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hR : ∀ n, 0 ≤ R n)
    (hbound : ∀ ε : ℝ, 0 < ε → ∀ n, R n ≤ ε * B + C n / (4 * ε))
    (hC : Tendsto C atTop (𝓝 0)) : Tendsto R atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop] at hC ⊢
  intro ε hε
  let δ : ℝ := ε / (2 * (B + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have ht : 0 < 2 * ε * δ := by positivity
  obtain ⟨N, hN⟩ := hC (2 * ε * δ) ht
  refine ⟨N, fun n hn => ?_⟩
  have hCn := hN n hn
  rw [Real.dist_eq, sub_zero] at hCn
  have hsmall : C n / (4 * δ) < ε / 2 := by
    apply (div_lt_iff₀ (by positivity : 0 < 4 * δ)).2
    have := lt_of_le_of_lt (le_abs_self (C n)) hCn
    nlinarith
  have hδB : δ * B < ε / 2 := by
    dsimp [δ]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (B + 1))).2
    nlinarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hR n)]
  linarith [hbound δ hδ n]

theorem tendsto_integral_sum_abs_cube_zero {ι : Type*}
    (s : ℕ → Finset ι) (D : ℕ → ι → Ω → ℝ)
    (hD : ∀ n i, i ∈ s n → AEStronglyMeasurable (D n i) μ)
    (h2 : ∀ n i, i ∈ s n → Integrable (fun ω => D n i ω ^ 2) μ)
    (h4 : ∀ n i, i ∈ s n → Integrable (fun ω => D n i ω ^ 4) μ)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ n, (∫ ω, ∑ i ∈ s n, D n i ω ^ 2 ∂μ) ≤ B)
    (hfourth : Tendsto (fun n => ∫ ω, ∑ i ∈ s n, D n i ω ^ 4 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, ∑ i ∈ s n, |D n i ω| ^ 3 ∂μ) atTop (𝓝 0) := by
  apply tendsto_zero_of_young_bound
    (C := fun n => ∫ ω, ∑ i ∈ s n, D n i ω ^ 4 ∂μ) hB
  · intro n
    exact integral_nonneg (fun ω => Finset.sum_nonneg (fun i _ => pow_nonneg (abs_nonneg _) _))
  · intro ε hε n
    have h := integral_sum_abs_cube_le (s n) (D n) (hD n) (h2 n) (h4 n) hε
    have hb := mul_le_mul_of_nonneg_left (hbound n) hε.le
    calc
      _ ≤ ε * (∫ ω, ∑ i ∈ s n, D n i ω ^ 2 ∂μ) +
          (1 / (4 * ε)) * (∫ ω, ∑ i ∈ s n, D n i ω ^ 4 ∂μ) := h
      _ ≤ ε * B + (1 / (4 * ε)) * (∫ ω, ∑ i ∈ s n, D n i ω ^ 4 ∂μ) :=
        add_le_add hb le_rfl
      _ = _ := by ring
  · exact hfourth

theorem ae_eq_add_of_taylor_L1_limits
    {Y L Q : Ω → ℝ} {Ln Qn : ℕ → Ω → ℝ}
    (hY : Integrable Y μ) (hL : Integrable L μ) (hQ : Integrable Q μ)
    (hLn : ∀ n, Integrable (Ln n) μ) (hQn : ∀ n, Integrable (Qn n) μ)
    (hrem : Tendsto (fun n => ∫ ω, |Y ω - Ln n ω - Qn n ω| ∂μ) atTop (𝓝 0))
    (hlin : Tendsto (fun n => ∫ ω, |Ln n ω - L ω| ∂μ) atTop (𝓝 0))
    (hquad : Tendsto (fun n => ∫ ω, |Qn n ω - Q ω| ∂μ) atTop (𝓝 0)) :
    Y =ᵐ[μ] fun ω => L ω + Q ω := by
  have hineq (n : ℕ) :
      (∫ ω, |Y ω - L ω - Q ω| ∂μ) ≤
        (∫ ω, |Y ω - Ln n ω - Qn n ω| ∂μ) +
        (∫ ω, |Ln n ω - L ω| ∂μ) + (∫ ω, |Qn n ω - Q ω| ∂μ) := by
    calc
      _ ≤ ∫ ω, |Y ω - Ln n ω - Qn n ω| +
          |Ln n ω - L ω| + |Qn n ω - Q ω| ∂μ := by
        apply integral_mono ((hY.sub hL).sub hQ).abs
          ((((hY.sub (hLn n)).sub (hQn n)).abs.add ((hLn n).sub hL).abs).add
            ((hQn n).sub hQ).abs)
        intro ω
        have he : Y ω - L ω - Q ω =
            (Y ω - Ln n ω - Qn n ω) + (Ln n ω - L ω) + (Qn n ω - Q ω) := by ring
        simp only [Pi.sub_apply, Pi.add_apply]
        rw [he]
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = _ := by
        have h1 : Integrable (fun ω => |Y ω - Ln n ω - Qn n ω|) μ :=
          ((hY.sub (hLn n)).sub (hQn n)).abs
        have h2 : Integrable (fun ω => |Ln n ω - L ω|) μ := ((hLn n).sub hL).abs
        have h3 : Integrable (fun ω => |Qn n ω - Q ω|) μ := ((hQn n).sub hQ).abs
        have h12 : Integrable (fun ω => |Y ω - Ln n ω - Qn n ω| + |Ln n ω - L ω|) μ := h1.add h2
        rw [integral_add h12 h3, integral_add h1 h2]

  have hz : (∫ ω, |Y ω - L ω - Q ω| ∂μ) = 0 := by
    apply le_antisymm
    · have hlim := (hrem.add hlin).add hquad
      simpa only [zero_add] using ge_of_tendsto hlim (Eventually.of_forall hineq)
    · exact integral_nonneg (fun _ => abs_nonneg _)
  have hae := (integral_eq_zero_iff_of_nonneg (fun ω => abs_nonneg (Y ω - L ω - Q ω))
    ((hY.sub hL).sub hQ).abs).1 hz
  filter_upwards [hae] with ω hω
  have hh := abs_eq_zero.mp hω
  linarith

end Problem367.MartingaleTaylorRemainder

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_TransformL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Problem367.MartingaleTransformL2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem condExp_increment_zero [IsFiniteMeasure μ]
    {ι : Type*} [Preorder ι] {F : Filtration ι mΩ} {M : ι → Ω → ℝ}
    (hM : Martingale M F μ) {s t : ι} (hst : s ≤ t) :
    μ[(fun ω => M t ω - M s ω) | F s] =ᵐ[μ] fun _ => 0 := by
  change μ[M t - M s | F s] =ᵐ[μ] fun _ => 0
  have hsub := condExp_sub (hM.integrable t) (hM.integrable s) (F s)
  have hs := hM.condExp_ae_eq (le_refl s)
  filter_upwards [hsub, hM.condExp_ae_eq hst, hs] with ω hω htω hsω
  simpa only [Pi.sub_apply, htω, hsω, sub_self] using hω

theorem bounded_mul_memLp_two {H D : Ω → ℝ} {K : ℝ}
    (hH : AEStronglyMeasurable H μ) (hD : MemLp D 2 μ)
    (hbound : ∀ᵐ ω ∂μ, |H ω| ≤ K) :
    MemLp (fun ω => H ω * D ω) 2 μ := by
  apply hD.of_le_mul (c := K) (hH.mul hD.aestronglyMeasurable)
  filter_upwards [hbound] with ω hω
  simpa only [Real.norm_eq_abs, Pi.mul_apply, abs_mul] using
    mul_le_mul_of_nonneg_right hω (abs_nonneg (D ω))

theorem integral_sq_transform [IsFiniteMeasure μ]
    {F : Filtration ℕ mΩ} {M H : ℕ → Ω → ℝ}
    (hM : Martingale M F μ) (hM2 : ∀ i, MemLp (M i) 2 μ)
    (hH : StronglyAdapted F H) {K : ℝ}
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |H i ω| ≤ K) (s : Finset ℕ) :
    (∫ ω, (∑ i ∈ s, H i ω * (M (i + 1) ω - M i ω)) ^ 2 ∂μ) =
      ∑ i ∈ s, ∫ ω, (H i ω * (M (i + 1) ω - M i ω)) ^ 2 ∂μ := by
  let D : ℕ → Ω → ℝ := fun i ω => M (i + 1) ω - M i ω
  have hD (i : ℕ) : StronglyMeasurable[F (i + 1)] (D i) :=
    (hM.stronglyMeasurable (i + 1)).sub
      ((hM.stronglyMeasurable i).mono (F.mono (Nat.le_succ i)))
  have hD2 (i : ℕ) : MemLp (D i) 2 μ := (hM2 (i + 1)).sub (hM2 i)
  have hHD (i : ℕ) : MemLp (fun ω => H i ω * D i ω) 2 μ :=
    bounded_mul_memLp_two ((hH i).mono (F.le i)).aestronglyMeasurable
      (hD2 i) (hbound i)
  have hzero (i : ℕ) : μ[D i | F i] =ᵐ[μ] 0 :=
    condExp_increment_zero hM (Nat.le_succ i)
  apply SimpleIntegral.integral_sq_sum_of_orthogonal s (fun i ω => H i ω * D i ω)
  · intro i hi j hj
    exact (hHD i).integrable_mul (hHD j)
  · intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact SimpleIntegral.predictable_increments_orthogonal F H D hH hD
        (fun i => (hD2 i).integrable (by norm_num)) hHD hzero hij
    · simpa only [mul_comm] using
        SimpleIntegral.predictable_increments_orthogonal F H D hH hD
          (fun i => (hD2 i).integrable (by norm_num)) hHD hzero hji

theorem sum_integral_sq_increment [IsFiniteMeasure μ]
    {F : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}
    (hM : Martingale M F μ) (hM2 : ∀ i, MemLp (M i) 2 μ) (n : ℕ) :
    (∑ i ∈ Finset.range n, ∫ ω, (M (i + 1) ω - M i ω) ^ 2 ∂μ) =
      ∫ ω, (M n ω - M 0 ω) ^ 2 ∂μ := by
  have h := integral_sq_transform hM hM2
    (H := fun _ _ => (1 : ℝ)) (fun _ => stronglyMeasurable_const)
    (K := 1) (fun _ => Filter.Eventually.of_forall (fun _ => by simp))
    (Finset.range n)
  simp only [one_mul] at h
  rw [← h]
  congr 1
  funext ω
  congr 1
  clear h
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

theorem integral_sq_transform_le [IsFiniteMeasure μ]
    {F : Filtration ℕ mΩ} {M H : ℕ → Ω → ℝ}
    (hM : Martingale M F μ) (hM2 : ∀ i, MemLp (M i) 2 μ)
    (hH : StronglyAdapted F H) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |H i ω| ≤ K) (n : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range n,
      H i ω * (M (i + 1) ω - M i ω)) ^ 2 ∂μ) ≤
      K ^ 2 * ∫ ω, (M n ω - M 0 ω) ^ 2 ∂μ := by
  rw [integral_sq_transform hM hM2 hH hbound,
    ← sum_integral_sq_increment hM hM2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hD2 := (hM2 (i + 1)).sub (hM2 i)
  have hHD := bounded_mul_memLp_two
    ((hH i).mono (F.le i)).aestronglyMeasurable hD2 (hbound i)
  rw [← integral_const_mul]
  apply integral_mono_ae hHD.integrable_sq (hD2.integrable_sq.const_mul (K ^ 2))
  filter_upwards [hbound i] with ω hω
  rw [mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).2 hω

theorem integral_sq_increment_eq [IsFiniteMeasure μ]
    {ι : Type*} [Preorder ι] {F : Filtration ι mΩ} {M : ι → Ω → ℝ}
    (hM : Martingale M F μ) {s t : ι} (hst : s ≤ t)
    (hs2 : MemLp (M s) 2 μ) (ht2 : MemLp (M t) 2 μ) :
    (∫ ω, (M t ω - M s ω) ^ 2 ∂μ) =
      (∫ ω, M t ω ^ 2 ∂μ) - ∫ ω, M s ω ^ 2 ∂μ := by
  have hD2 : MemLp (fun ω => M t ω - M s ω) 2 μ := ht2.sub hs2
  have hcross : Integrable (fun ω => M s ω * (M t ω - M s ω)) μ :=
    hs2.integrable_mul hD2
  have horth : (∫ ω, M s ω * (M t ω - M s ω) ∂μ) = 0 :=
    SimpleIntegral.integral_mul_eq_zero_of_condExp_eq_zero (F.le s)
      (hM.stronglyMeasurable s) (hD2.integrable (by norm_num)) hcross
      (condExp_increment_zero hM hst)
  have heq : (∫ ω, M t ω ^ 2 ∂μ) =
      (∫ ω, (M t ω - M s ω) ^ 2 ∂μ) +
        2 * (∫ ω, M s ω * (M t ω - M s ω) ∂μ) +
          ∫ ω, M s ω ^ 2 ∂μ := by
    calc
      _ = ∫ ω, (M t ω - M s ω) ^ 2 +
          2 * (M s ω * (M t ω - M s ω)) + M s ω ^ 2 ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun ω => by ring)
      _ = _ := by
        have h1 := integral_add hD2.integrable_sq (hcross.const_mul 2)
        have h2 := integral_add (hD2.integrable_sq.add (hcross.const_mul 2)) hs2.integrable_sq
        simp only [Pi.add_apply] at h1 h2
        rw [h1, integral_const_mul] at h2
        exact h2
  rw [horth] at heq
  linarith

theorem integral_sq_increment_le [IsFiniteMeasure μ]
    {ι : Type*} [Preorder ι] {F : Filtration ι mΩ} {M : ι → Ω → ℝ}
    (hM : Martingale M F μ) {s t : ι} (hst : s ≤ t)
    (hs2 : MemLp (M s) 2 μ) (ht2 : MemLp (M t) 2 μ) :
    (∫ ω, (M t ω - M s ω) ^ 2 ∂μ) ≤ ∫ ω, M t ω ^ 2 ∂μ := by
  rw [integral_sq_increment_eq hM hst hs2 ht2]
  exact sub_le_self _ (integral_nonneg (fun ω => sq_nonneg _))

theorem integral_sq_grid_transform_le_terminal [IsFiniteMeasure μ]
    {ι : Type*} [Preorder ι] {F : Filtration ι mΩ} {M : ι → Ω → ℝ}
    (hM : Martingale M F μ) (hM2 : ∀ t, MemLp (M t) 2 μ)
    (t : ℕ → ι) (ht : Monotone t) (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[F (t i)] (H i)) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |H i ω| ≤ K) (n : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range n,
      H i ω * (M (t (i + 1)) ω - M (t i) ω)) ^ 2 ∂μ) ≤
      K ^ 2 * ∫ ω, M (t n) ω ^ 2 ∂μ := by
  let G : Filtration ℕ mΩ :=
    ⟨fun i => F (t i), fun _ _ hij => F.mono (ht hij), fun i => F.le (t i)⟩
  have hMG : Martingale (fun i => M (t i)) G μ :=
    ⟨by intro i; exact hM.stronglyMeasurable (t i),
      by intro i j hij; exact hM.condExp_ae_eq (ht hij)⟩
  exact (integral_sq_transform_le hMG (fun i => hM2 (t i)) hH hK hbound n).trans
    (mul_le_mul_of_nonneg_left
      (integral_sq_increment_le hM (ht (Nat.zero_le n)) (hM2 _) (hM2 _)) (sq_nonneg K))

end Problem367.MartingaleTransformL2

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_BoundedMartingaleVariation
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal

namespace Problem367.BoundedMartingaleVariation

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem bounded_pow_memLp_two [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) {C : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ᵐ ω ∂μ, |f ω| ≤ C) (p : ℕ) :
    MemLp (fun ω => f ω ^ p) 2 μ := by
  apply MemLp.of_bound (hf.pow p) (C ^ p)
  filter_upwards [hb] with ω hω
  simp only [Pi.pow_apply, norm_pow, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) hω p

theorem sum_sq_increment (x : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (x (i + 1) - x i) ^ 2) =
      x n ^ 2 - x 0 ^ 2 - 2 * ∑ i ∈ Finset.range n, x i * (x (i + 1) - x i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

theorem sq_sum_sq_increment_le (x : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (x (i + 1) - x i) ^ 2) ^ 2 ≤
      4 * x n ^ 4 + 4 * x 0 ^ 4 +
        8 * (∑ i ∈ Finset.range n, x i * (x (i + 1) - x i)) ^ 2 := by
  rw [sum_sq_increment]
  have h1 : (x n ^ 2 - x 0 ^ 2) ^ 2 ≤ 2 * (x n ^ 2) ^ 2 + 2 * (x 0 ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (x n ^ 2 + x 0 ^ 2)]
  have h2 : (x n ^ 2 - x 0 ^ 2 -
      2 * ∑ i ∈ Finset.range n, x i * (x (i + 1) - x i)) ^ 2 ≤
      2 * (x n ^ 2 - x 0 ^ 2) ^ 2 +
        8 * (∑ i ∈ Finset.range n, x i * (x (i + 1) - x i)) ^ 2 := by
    nlinarith [sq_nonneg (x n ^ 2 - x 0 ^ 2 +
      2 * ∑ i ∈ Finset.range n, x i * (x (i + 1) - x i))]
  nlinarith

theorem integral_sq_quadratic_variation_le [IsProbabilityMeasure μ]
    {F : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ} (hM : Martingale M F μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ i, ∀ᵐ ω ∂μ, |M i ω| ≤ C) (n : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range n, (M (i + 1) ω - M i ω) ^ 2) ^ 2 ∂μ) ≤
      16 * C ^ 4 := by
  have hm (i : ℕ) : AEStronglyMeasurable (M i) μ :=
    ((hM.stronglyMeasurable i).mono (F.le i)).aestronglyMeasurable
  have hM2 (i : ℕ) : MemLp (M i) 2 μ := by
    simpa using bounded_pow_memLp_two (hm i) hC (hb i) 1
  have hD (i : ℕ) : ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ 2 * C := by
    filter_upwards [hb (i + 1), hb i] with ω hnext hnow
    calc
      |M (i + 1) ω - M i ω| ≤ |M (i + 1) ω| + |M i ω| := abs_sub _ _
      _ ≤ 2 * C := by linarith
  have hQ2 : MemLp (fun ω => ∑ i ∈ Finset.range n,
      (M (i + 1) ω - M i ω) ^ 2) 2 μ := by
    exact memLp_finsetSum _ (fun i hi =>
      bounded_pow_memLp_two ((hm (i + 1)).sub (hm i)) (by positivity) (hD i) 2)
  have hS2 : MemLp (fun ω => ∑ i ∈ Finset.range n,
      M i ω * (M (i + 1) ω - M i ω)) 2 μ := by
    exact memLp_finsetSum _ (fun i hi =>
      MartingaleTransformL2.bounded_mul_memLp_two (hm i)
        ((hM2 (i + 1)).sub (hM2 i)) (hb i))
  have hpowInt (i : ℕ) : Integrable (fun ω => M i ω ^ 4) μ :=
    (bounded_pow_memLp_two (hm i) hC (hb i) 4).integrable (by norm_num)
  have hpowbound (i p : ℕ) (hp : Even p) : (∫ ω, M i ω ^ p ∂μ) ≤ C ^ p := by
    calc
      _ ≤ ∫ _ : Ω, C ^ p ∂μ := by
        apply integral_mono_ae
          ((bounded_pow_memLp_two (hm i) hC (hb i) p).integrable (by norm_num))
          (integrable_const _)
        filter_upwards [hb i] with ω hω
        simpa only [hp.pow_abs] using pow_le_pow_left₀ (abs_nonneg _) hω p
      _ = _ := by simp
  have hSbound : (∫ ω, (∑ i ∈ Finset.range n,
      M i ω * (M (i + 1) ω - M i ω)) ^ 2 ∂μ) ≤ C ^ 4 := by
    have h := MartingaleTransformL2.integral_sq_grid_transform_le_terminal
      hM hM2 (fun i : ℕ => i) monotone_id M hM.stronglyAdapted hC hb n
    exact h.trans (by
      calc
        C ^ 2 * (∫ ω, M n ω ^ 2 ∂μ) ≤ C ^ 2 * C ^ 2 :=
          mul_le_mul_of_nonneg_left (hpowbound n 2 (by decide)) (sq_nonneg C)
        _ = C ^ 4 := by ring)
  have hmajor : (∫ ω, (∑ i ∈ Finset.range n,
      (M (i + 1) ω - M i ω) ^ 2) ^ 2 ∂μ) ≤
      4 * (∫ ω, M n ω ^ 4 ∂μ) + 4 * (∫ ω, M 0 ω ^ 4 ∂μ) +
        8 * (∫ ω, (∑ i ∈ Finset.range n,
          M i ω * (M (i + 1) ω - M i ω)) ^ 2 ∂μ) := by
    calc
      _ ≤ ∫ ω, 4 * M n ω ^ 4 + 4 * M 0 ω ^ 4 +
          8 * (∑ i ∈ Finset.range n, M i ω * (M (i + 1) ω - M i ω)) ^ 2 ∂μ := by
        apply integral_mono_ae hQ2.integrable_sq
          (((hpowInt n).const_mul 4).add ((hpowInt 0).const_mul 4) |>.add
            (hS2.integrable_sq.const_mul 8))
        exact Filter.Eventually.of_forall (fun ω => sq_sum_sq_increment_le (fun i => M i ω) n)
      _ = _ := by
        have h1 := integral_add ((hpowInt n).const_mul 4) ((hpowInt 0).const_mul 4)
        have h2 := integral_add
          (((hpowInt n).const_mul 4).add ((hpowInt 0).const_mul 4))
          (hS2.integrable_sq.const_mul 8)
        simp only [Pi.add_apply] at h1 h2
        rw [h1] at h2
        simpa only [integral_const_mul] using h2
  nlinarith [hpowbound n 4 (by decide), hpowbound 0 4 (by decide)]

theorem incrementModulus_nonneg (x : ℕ → ℝ) (n : ℕ) :
    0 ≤ incrementModulus x n := NNReal.coe_nonneg _

theorem abs_increment_le_modulus (x : ℕ → ℝ) {i n : ℕ} (hi : i < n) :
    |x (i + 1) - x i| ≤ incrementModulus x n := by
  have h := Finset.le_sup (f := fun j => ‖x (j + 1) - x j‖₊) (Finset.mem_range.mpr hi)
  exact_mod_cast h

theorem incrementModulus_le (x : ℕ → ℝ) (n : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i < n, |x (i + 1) - x i| ≤ C) : incrementModulus x n ≤ C := by
  have h : (Finset.range n).sup (fun i => ‖x (i + 1) - x i‖₊) ≤ (⟨C, hC⟩ : ℝ≥0) := by
    apply Finset.sup_le
    intro i hi
    exact_mod_cast hb i (Finset.mem_range.mp hi)
  exact_mod_cast h

theorem stronglyMeasurable_incrementModulus (x : ℕ → Ω → ℝ)
    (hx : ∀ i, StronglyMeasurable (x i)) (n : ℕ) :
    StronglyMeasurable (fun ω => incrementModulus (fun i => x i ω) n) := by
  induction n with
  | zero => simpa [incrementModulus] using (stronglyMeasurable_const :
      StronglyMeasurable (fun _ : Ω => (0 : ℝ)))
  | succ n ih =>
    have h := ((((hx (n + 1)).measurable.sub (hx n).measurable).norm).max
      ih.measurable).stronglyMeasurable
    simpa only [incrementModulus, Finset.range_add_one, Finset.sup_insert,
      NNReal.coe_max, coe_nnnorm, Real.norm_eq_abs, Pi.sub_apply] using h

theorem tendsto_incrementModulus_of_uniformContinuousOn
    {I : Type*} [PseudoMetricSpace I] {S : Set I} {x : I → ℝ}
    (hx : UniformContinuousOn x S) (t : ℕ → ℕ → I) (N : ℕ → ℕ)
    (hmem : ∀ k i, i ≤ N k → t k i ∈ S) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hmesh : ∀ k i, i < N k → dist (t k (i + 1)) (t k i) ≤ δ k) :
    Tendsto (fun k => incrementModulus (fun i => x (t k i)) (N k)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨η, hη, hlocal⟩ := Metric.uniformContinuousOn_iff.mp hx (ε / 2) (by positivity)
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hδ η hη
  refine ⟨K, fun k hk => ?_⟩
  have hδk : δ k < η := by
    have hdk := hK k hk
    rw [Real.dist_eq, sub_zero] at hdk
    exact lt_of_le_of_lt (le_abs_self _) hdk
  have hmod : incrementModulus (fun i => x (t k i)) (N k) ≤ ε / 2 := by
    apply incrementModulus_le _ _ (by positivity)
    intro i hi
    have hdist := hlocal (t k (i + 1)) (hmem k _ hi) (t k i) (hmem k _ hi.le)
      (lt_of_le_of_lt (hmesh k i hi) hδk)
    exact le_of_lt (by simpa only [Real.dist_eq] using hdist)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (incrementModulus_nonneg _ _)]
  linarith

theorem mul_le_young (a b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    a * b ≤ ε * b ^ 2 + a ^ 2 / (4 * ε) := by
  have hε0 : ε ≠ 0 := ne_of_gt hε
  have hid : (4 * ε) * (ε * b ^ 2 + a ^ 2 / (4 * ε) - a * b) =
      (2 * ε * b - a) ^ 2 := by
    field_simp
    ring
  have hnon : 0 ≤ ε * b ^ 2 + a ^ 2 / (4 * ε) - a * b := by
    apply (mul_nonneg_iff_of_pos_left (by positivity : 0 < 4 * ε)).1
    rw [hid]
    exact sq_nonneg _
  linarith

theorem tendsto_integral_sum_fourth_of_modulus [IsProbabilityMeasure μ]
    (F : ℕ → Filtration ℕ mΩ) (M : ℕ → ℕ → Ω → ℝ)
    (hM : ∀ k, Martingale (M k) (F k) μ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ k i, ∀ᵐ ω ∂μ, |M k i ω| ≤ C) (N : ℕ → ℕ)
    (hmod : ∀ᵐ ω ∂μ, Tendsto
      (fun k => incrementModulus (fun i => M k i ω) (N k)) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, ∑ i ∈ Finset.range (N k),
      (M k (i + 1) ω - M k i ω) ^ 4 ∂μ) atTop (𝓝 0) := by
  let D : ℕ → ℕ → Ω → ℝ := fun k i ω => M k (i + 1) ω - M k i ω
  let R : ℕ → Ω → ℝ := fun k ω => incrementModulus (fun i => M k i ω) (N k)
  let Q : ℕ → Ω → ℝ := fun k ω => ∑ i ∈ Finset.range (N k), D k i ω ^ 2
  have hm (k i : ℕ) : StronglyMeasurable (M k i) :=
    ((hM k).stronglyMeasurable i).mono ((F k).le i)
  have hDm (k i : ℕ) : AEStronglyMeasurable (D k i) μ :=
    ((hm k (i + 1)).sub (hm k i)).aestronglyMeasurable
  have hDb (k i : ℕ) : ∀ᵐ ω ∂μ, |D k i ω| ≤ 2 * C := by
    filter_upwards [hb k (i + 1), hb k i] with ω hn hi
    exact (abs_sub _ _).trans (by linarith)
  have hDp (k i p : ℕ) : MemLp (fun ω => D k i ω ^ p) 2 μ :=
    bounded_pow_memLp_two (hDm k i) (by positivity) (hDb k i) p
  have hRm (k : ℕ) : StronglyMeasurable (R k) :=
    stronglyMeasurable_incrementModulus (M k) (hm k) (N k)
  have hRb (k : ℕ) : ∀ᵐ ω ∂μ, |R k ω| ≤ 2 * C := by
    filter_upwards [ae_all_iff.2 (hDb k)] with ω hω
    rw [abs_of_nonneg (incrementModulus_nonneg _ _)]
    exact incrementModulus_le _ _ (by positivity) (fun i hi => hω i)
  have hRp (k p : ℕ) : MemLp (fun ω => R k ω ^ p) 2 μ :=
    bounded_pow_memLp_two (hRm k).aestronglyMeasurable (by positivity) (hRb k) p
  have hQ2 (k : ℕ) : MemLp (Q k) 2 μ :=
    memLp_finsetSum _ (fun i hi => hDp k i 2)
  have hQbound (k : ℕ) : (∫ ω, Q k ω ^ 2 ∂μ) ≤ 16 * C ^ 4 :=
    integral_sq_quadratic_variation_le (hM k) hC (hb k) (N k)
  have hRlim : Tendsto (fun k => ∫ ω, R k ω ^ 4 ∂μ) atTop (𝓝 0) := by
    have hdom (k : ℕ) : ∀ᵐ ω ∂μ, ‖R k ω ^ 4‖ ≤ (2 * C) ^ 4 := by
      filter_upwards [hRb k] with ω hω
      rw [norm_pow, Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hω 4
    have h := tendsto_integral_of_dominated_convergence (μ := μ)
      (fun _ : Ω => (2 * C) ^ 4) (fun k => (hRm k).aestronglyMeasurable.pow 4)
      (integrable_const _) hdom
      (hmod.mono (fun ω hω => by simpa using hω.pow 4))
    simpa using h
  apply MartingaleTaylorRemainder.tendsto_zero_of_young_bound
    (C := fun k => ∫ ω, R k ω ^ 4 ∂μ) (B := 16 * C ^ 4) (by positivity)
  · intro k
    exact integral_nonneg (fun ω => Finset.sum_nonneg (fun i hi => by positivity))
  · intro ε hε k
    have hfourInt : Integrable (fun ω => ∑ i ∈ Finset.range (N k), D k i ω ^ 4) μ :=
      integrable_finsetSum _ (fun i hi => (hDp k i 4).integrable (by norm_num))
    have hpoint (ω : Ω) : (∑ i ∈ Finset.range (N k), D k i ω ^ 4) ≤
        ε * Q k ω ^ 2 + R k ω ^ 4 / (4 * ε) := by
      have hsum : (∑ i ∈ Finset.range (N k), D k i ω ^ 4) ≤ R k ω ^ 2 * Q k ω := by
        dsimp only [Q]
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i hi
        have habs : |D k i ω| ≤ R k ω :=
          abs_increment_le_modulus (fun i => M k i ω) (Finset.mem_range.mp hi)
        have hsq : D k i ω ^ 2 ≤ R k ω ^ 2 := by
          simpa only [sq_abs] using
            (sq_le_sq₀ (abs_nonneg _) (incrementModulus_nonneg _ _)).2 habs
        nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg (D k i ω))]
      exact hsum.trans (by
        have hh := mul_le_young (R k ω ^ 2) (Q k ω) hε
        have heq : (R k ω ^ 2) ^ 2 = R k ω ^ 4 := by ring
        rw [heq] at hh
        exact hh)
    calc
      _ ≤ ∫ ω, ε * Q k ω ^ 2 + R k ω ^ 4 / (4 * ε) ∂μ :=
        integral_mono hfourInt
          (((hQ2 k).integrable_sq.const_mul ε).add
            (((hRp k 4).integrable (by norm_num)).div_const (4 * ε))) hpoint
      _ = ε * (∫ ω, Q k ω ^ 2 ∂μ) + (∫ ω, R k ω ^ 4 ∂μ) / (4 * ε) := by
        rw [integral_add ((hQ2 k).integrable_sq.const_mul ε)
          (((hRp k 4).integrable (by norm_num)).div_const (4 * ε)),
          integral_const_mul, integral_div]
      _ ≤ ε * (16 * C ^ 4) + (∫ ω, R k ω ^ 4 ∂μ) / (4 * ε) :=
        add_le_add (mul_le_mul_of_nonneg_left (hQbound k) hε.le) le_rfl
  · exact hRlim

theorem tendsto_integral_sum_fourth_of_continuous [IsProbabilityMeasure μ]
    {I : Type*} [Preorder I] [PseudoMetricSpace I]
    {F : Filtration I mΩ} {M : I → Ω → ℝ} (hM : Martingale M F μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ t, ∀ᵐ ω ∂μ, |M t ω| ≤ C)
    {S : Set I} (hS : IsCompact S) (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => M t ω) S)
    (t : ℕ → ℕ → I) (ht : ∀ k, Monotone (t k)) (N : ℕ → ℕ)
    (hmem : ∀ k i, i ≤ N k → t k i ∈ S) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hmesh : ∀ k i, i < N k → dist (t k (i + 1)) (t k i) ≤ δ k) :
    Tendsto (fun k => ∫ ω, ∑ i ∈ Finset.range (N k),
      (M (t k (i + 1)) ω - M (t k i) ω) ^ 4 ∂μ) atTop (𝓝 0) := by
  let G : ℕ → Filtration ℕ mΩ := fun k =>
    ⟨fun i => F (t k i), fun _ _ hij => F.mono (ht k hij), fun i => F.le (t k i)⟩
  have hMG (k : ℕ) : Martingale (fun i => M (t k i)) (G k) μ :=
    ⟨fun i => hM.stronglyMeasurable _, fun _ _ hij => hM.condExp_ae_eq (ht k hij)⟩
  apply tendsto_integral_sum_fourth_of_modulus G (fun k i => M (t k i)) hMG hC
    (fun k i => hb (t k i)) N
  filter_upwards [hc] with ω hω
  exact tendsto_incrementModulus_of_uniformContinuousOn
    (hS.uniformContinuousOn_of_continuous hω) t N hmem δ hδ hmesh

theorem tendsto_sum_integral_fourth_of_continuous [IsProbabilityMeasure μ]
    {I : Type*} [Preorder I] [PseudoMetricSpace I]
    {F : Filtration I mΩ} {M : I → Ω → ℝ} (hM : Martingale M F μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ t, ∀ᵐ ω ∂μ, |M t ω| ≤ C)
    {S : Set I} (hS : IsCompact S) (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => M t ω) S)
    (t : ℕ → ℕ → I) (ht : ∀ k, Monotone (t k)) (N : ℕ → ℕ)
    (hmem : ∀ k i, i ≤ N k → t k i ∈ S) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hmesh : ∀ k i, i < N k → dist (t k (i + 1)) (t k i) ≤ δ k) :
    Tendsto (fun k => ∑ i ∈ Finset.range (N k),
      ∫ ω, (M (t k (i + 1)) ω - M (t k i) ω) ^ 4 ∂μ) atTop (𝓝 0) := by
  apply (tendsto_integral_sum_fourth_of_continuous hM hC hb hS hc t ht N hmem δ hδ hmesh).congr'
  apply Filter.Eventually.of_forall
  intro k
  apply integral_finsetSum
  intro i hi
  have hm : AEStronglyMeasurable (fun ω => M (t k (i + 1)) ω - M (t k i) ω) μ :=
    (((hM.stronglyMeasurable _).mono (F.le _)).sub
      ((hM.stronglyMeasurable _).mono (F.le _))).aestronglyMeasurable
  apply (bounded_pow_memLp_two hm (show 0 ≤ 2 * C by positivity) ?_ 4).integrable (by norm_num)
  filter_upwards [hb (t k (i + 1)), hb (t k i)] with ω hn hi
  exact (abs_sub _ _).trans (by linarith)

end Problem367.BoundedMartingaleVariation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_QuadraticVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators

namespace Problem367.MartingaleQuadraticVariation

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem condExp_increment_eq_zero [IsFiniteMeasure μ]
    {I : Type*} [Preorder I] {ℱ : Filtration I mΩ}
    {M : I → Ω → ℝ} (hM : Martingale M ℱ μ) {s t : I} (hst : s ≤ t) :
    μ[increment M s t | ℱ s] =ᵐ[μ] 0 := by
  have hsub := condExp_sub (hM.integrable t) (hM.integrable s) (ℱ s)
  filter_upwards [hsub, hM.condExp_ae_eq hst, hM.condExp_ae_eq (le_refl s)]
    with ω hs ht hself
  simp only [Pi.sub_apply] at hs
  change μ[M t - M s | ℱ s] ω = 0
  rw [hs, ht, hself, sub_self]

theorem integrable_compensator [IsFiniteMeasure μ]
    {I : Type*} [Preorder I] {ℱ : Filtration I mΩ}
    {M A : I → Ω → ℝ}
    (hQ : Martingale (fun t ω => (M t ω) ^ 2 - A t ω) ℱ μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ) (t : I) : Integrable (A t) μ := by
  simpa only [Pi.sub_def, sub_sub_cancel] using
    (hM2 t).integrable_sq.sub (hQ.integrable t)

theorem stronglyAdapted_compensator
    {I : Type*} [Preorder I] {ℱ : Filtration I mΩ}
    {M A : I → Ω → ℝ} (hM : Martingale M ℱ μ)
    (hQ : Martingale (fun t ω => (M t ω) ^ 2 - A t ω) ℱ μ) :
    StronglyAdapted ℱ A := by
  intro t
  simpa only [Pi.sub_def, Pi.pow_apply, sub_sub_cancel] using
    ((hM.stronglyMeasurable t).pow 2).sub (hQ.stronglyMeasurable t)

theorem condExp_squareError_eq_zero [IsFiniteMeasure μ]
    {I : Type*} [Preorder I] {ℱ : Filtration I mΩ}
    {M A : I → Ω → ℝ} (hM : Martingale M ℱ μ)
    (hQ : Martingale (fun t ω => (M t ω) ^ 2 - A t ω) ℱ μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ) {s t : I} (hst : s ≤ t) :
    μ[squareError M A s t | ℱ s] =ᵐ[μ] 0 := by
  let Q : I → Ω → ℝ := fun r ω => (M r ω) ^ 2 - A r ω
  have hd : Integrable (increment M s t) μ := (hM.integrable t).sub (hM.integrable s)
  have hprod : Integrable (M s * increment M s t) μ :=
    (hM2 s).integrable_mul ((hM2 t).sub (hM2 s))
  have hpull := condExp_mul_of_stronglyMeasurable_left
    (hM.stronglyMeasurable s) hprod hd
  have hpzero : μ[M s * increment M s t | ℱ s] =ᵐ[μ] 0 := by
    filter_upwards [hpull, condExp_increment_eq_zero hM hst] with ω hp hz
    simp only [Pi.mul_apply, Pi.zero_apply] at hp hz ⊢
    rw [hp, hz, mul_zero]
  have hident : squareError M A s t =
      increment Q s t - (2 : ℝ) • (M s * increment M s t) := by
    funext ω
    simp only [squareError, increment, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.mul_apply, Q]
    ring
  rw [hident]
  have hsub : μ[increment Q s t - (2 : ℝ) • (M s * increment M s t) | ℱ s] =ᵐ[μ]
      μ[increment Q s t | ℱ s] - μ[(2 : ℝ) • (M s * increment M s t) | ℱ s] :=
    condExp_sub ((hQ.integrable t).sub (hQ.integrable s))
      (hprod.smul (2 : ℝ)) (ℱ s)
  have hscale := condExp_smul (μ := μ) (m := ℱ s) (2 : ℝ)
    (M s * increment M s t)
  filter_upwards [hsub, condExp_increment_eq_zero hQ hst, hpzero, hscale]
    with ω hs hq hp hc
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hs hq hp hc ⊢
  change μ[increment Q s t | ℱ s] ω = 0 at hq
  rw [hs, hq, hc, hp]
  ring

theorem stronglyMeasurable_squareError
    {I : Type*} [Preorder I] {ℱ : Filtration I mΩ}
    {M A : I → Ω → ℝ} (hM : Martingale M ℱ μ)
    (hQ : Martingale (fun t ω => (M t ω) ^ 2 - A t ω) ℱ μ)
    {s t : I} (hst : s ≤ t) : StronglyMeasurable[ℱ t] (squareError M A s t) := by
  have hA := stronglyAdapted_compensator hM hQ
  exact (((hM.stronglyMeasurable t).sub
    ((hM.stronglyMeasurable s).mono (ℱ.mono hst))).pow 2).sub
      ((hA t).sub ((hA s).mono (ℱ.mono hst)))

theorem integrable_squareError [IsFiniteMeasure μ]
    {I : Type*} [Preorder I] {ℱ : Filtration I mΩ}
    {M A : I → Ω → ℝ}
    (hQ : Martingale (fun t ω => (M t ω) ^ 2 - A t ω) ℱ μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ) (s t : I) :
    Integrable (squareError M A s t) μ :=
  ((hM2 t).sub (hM2 s)).integrable_sq.sub
    ((integrable_compensator hQ hM2 t).sub (integrable_compensator hQ hM2 s))

theorem weighted_error_isometry [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ mΩ} {M A H : ℕ → Ω → ℝ}
    (hM : Martingale M ℱ μ)
    (hQ : Martingale (fun t ω => (M t ω) ^ 2 - A t ω) ℱ μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ)
    (hH : ∀ i, StronglyMeasurable[ℱ i] (H i))
    (hY2 : ∀ i, MemLp (fun ω => H i ω * squareError M A i (i + 1) ω) 2 μ)
    (s : Finset ℕ) :
    (∫ ω, (∑ i ∈ s, H i ω * squareError M A i (i + 1) ω) ^ 2 ∂μ) =
      ∑ i ∈ s, ∫ ω, (H i ω * squareError M A i (i + 1) ω) ^ 2 ∂μ := by
  let D : ℕ → Ω → ℝ := fun i => squareError M A i (i + 1)
  have hD (i : ℕ) : StronglyMeasurable[ℱ (i + 1)] (D i) :=
    stronglyMeasurable_squareError hM hQ (Nat.le_succ i)
  have hDint (i : ℕ) : Integrable (D i) μ := integrable_squareError hQ hM2 _ _
  have hzero (i : ℕ) : μ[D i | ℱ i] =ᵐ[μ] 0 :=
    condExp_squareError_eq_zero hM hQ hM2 (Nat.le_succ i)
  apply SimpleIntegral.integral_sq_sum_of_orthogonal
  · intro i _ j _
    exact (hY2 i).integrable_mul (hY2 j)
  · intro i _ j _ hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact SimpleIntegral.predictable_increments_orthogonal
        ℱ H D hH hD hDint hY2 hzero hij
    · simpa only [mul_comm] using
        SimpleIntegral.predictable_increments_orthogonal ℱ H D hH hD hDint hY2 hzero hji

theorem weighted_error_sq_le {h x a K : ℝ} (hK : 0 ≤ K) (hh : |h| ≤ K) :
    (h * (x ^ 2 - a)) ^ 2 ≤ 2 * K ^ 2 * (x ^ 4 + a ^ 2) := by
  have hh2 : h ^ 2 ≤ K ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg h) hK).2 hh
  have he : (x ^ 2 - a) ^ 2 ≤ 2 * (x ^ 4 + a ^ 2) := by
    nlinarith [sq_nonneg (x ^ 2 + a)]
  calc
    (h * (x ^ 2 - a)) ^ 2 = h ^ 2 * (x ^ 2 - a) ^ 2 := mul_pow _ _ _
    _ ≤ K ^ 2 * (x ^ 2 - a) ^ 2 := mul_le_mul_of_nonneg_right hh2 (sq_nonneg _)
    _ ≤ K ^ 2 * (2 * (x ^ 4 + a ^ 2)) := mul_le_mul_of_nonneg_left he (sq_nonneg _)
    _ = 2 * K ^ 2 * (x ^ 4 + a ^ 2) := by ring

theorem integral_weighted_error_sq_le [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ mΩ} {M A H : ℕ → Ω → ℝ}
    (hM : Martingale M ℱ μ)
    (hQ : Martingale (fun t ω => (M t ω) ^ 2 - A t ω) ℱ μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ)
    (hH : ∀ i, StronglyMeasurable[ℱ i] (H i))
    (hD4 : ∀ i, MemLp (fun ω => (increment M i (i + 1) ω) ^ 2) 2 μ)
    (hA2 : ∀ i, MemLp (increment A i (i + 1)) 2 μ)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ i, ∀ᵐ ω ∂μ, |H i ω| ≤ K)
    (s : Finset ℕ) :
    (∫ ω, (∑ i ∈ s, H i ω * squareError M A i (i + 1) ω) ^ 2 ∂μ) ≤
      2 * K ^ 2 * ∑ i ∈ s,
        ((∫ ω, (increment M i (i + 1) ω) ^ 4 ∂μ) +
          ∫ ω, (increment A i (i + 1) ω) ^ 2 ∂μ) := by
  have hY2 (i : ℕ) : MemLp (fun ω => H i ω * squareError M A i (i + 1) ω) 2 μ := by
    have hHtop : MemLp (H i) ⊤ μ := memLp_top_of_bound
      ((hH i).mono (ℱ.le i)).aestronglyMeasurable K (by simpa only [Real.norm_eq_abs] using hbound i)
    exact MeasureTheory.MemLp.mul' (hφ := hHtop) (hf := ((hD4 i).sub (hA2 i)))
  rw [weighted_error_isometry hM hQ hM2 hH hY2 s, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hfour : Integrable (fun ω => (increment M i (i + 1) ω) ^ 4) μ := by
    simpa only [← pow_mul] using (hD4 i).integrable_sq
  calc
    (∫ ω, (H i ω * squareError M A i (i + 1) ω) ^ 2 ∂μ) ≤
        ∫ ω, 2 * K ^ 2 * ((increment M i (i + 1) ω) ^ 4 +
          (increment A i (i + 1) ω) ^ 2) ∂μ := by
      apply integral_mono_ae (hY2 i).integrable_sq
        ((hfour.add (hA2 i).integrable_sq).const_mul _)
      filter_upwards [hbound i] with ω hω
      exact weighted_error_sq_le hK hω
    _ = _ := by rw [integral_const_mul, integral_add hfour (hA2 i).integrable_sq]

theorem integral_grid_weighted_error_sq_le [IsFiniteMeasure μ]
    {I : Type*} [Preorder I] {ℱ : Filtration I mΩ} {M A : I → Ω → ℝ}
    (hM : Martingale M ℱ μ)
    (hQ : Martingale (fun t ω => (M t ω) ^ 2 - A t ω) ℱ μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ)
    (t : ℕ → I) (ht : Monotone t) (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[ℱ (t i)] (H i))
    (hD4 : ∀ i, MemLp (fun ω => (increment M (t i) (t (i + 1)) ω) ^ 2) 2 μ)
    (hA2 : ∀ i, MemLp (increment A (t i) (t (i + 1))) 2 μ)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ i, ∀ᵐ ω ∂μ, |H i ω| ≤ K)
    (s : Finset ℕ) :
    (∫ ω, (∑ i ∈ s, H i ω * squareError M A (t i) (t (i + 1)) ω) ^ 2 ∂μ) ≤
      2 * K ^ 2 * ∑ i ∈ s,
        ((∫ ω, (increment M (t i) (t (i + 1)) ω) ^ 4 ∂μ) +
          ∫ ω, (increment A (t i) (t (i + 1)) ω) ^ 2 ∂μ) := by
  let G : Filtration ℕ mΩ :=
    ⟨fun i => ℱ (t i), fun _ _ hij => ℱ.mono (ht hij), fun i => ℱ.le (t i)⟩
  have hMG : Martingale (fun i => M (t i)) G μ :=
    ⟨fun i => hM.stronglyMeasurable (t i), fun _ _ hij => hM.condExp_ae_eq (ht hij)⟩
  have hQG : Martingale (fun i ω => (M (t i) ω) ^ 2 - A (t i) ω) G μ :=
    ⟨fun i => hQ.stronglyMeasurable (t i), fun _ _ hij => hQ.condExp_ae_eq (ht hij)⟩
  exact integral_weighted_error_sq_le hMG hQG (fun i => hM2 (t i))
    hH hD4 hA2 hK hbound s

theorem tendsto_integral_grid_weighted_error_sq [IsFiniteMeasure μ]
    {I : Type*} [Preorder I] {ℱ : Filtration I mΩ} {M A : I → Ω → ℝ}
    (hM : Martingale M ℱ μ)
    (hQ : Martingale (fun t ω => (M t ω) ^ 2 - A t ω) ℱ μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ)
    (t : ℕ → ℕ → I) (ht : ∀ n, Monotone (t n)) (H : ℕ → ℕ → Ω → ℝ)
    (hH : ∀ n i, StronglyMeasurable[ℱ (t n i)] (H n i))
    (hD4 : ∀ n i,
      MemLp (fun ω => (increment M (t n i) (t n (i + 1)) ω) ^ 2) 2 μ)
    (hA2 : ∀ n i, MemLp (increment A (t n i) (t n (i + 1))) 2 μ)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ n i, ∀ᵐ ω ∂μ, |H n i ω| ≤ K)
    (s : ℕ → Finset ℕ)
    (hsmall : Tendsto (fun n => ∑ i ∈ s n,
      ((∫ ω, (increment M (t n i) (t n (i + 1)) ω) ^ 4 ∂μ) +
        ∫ ω, (increment A (t n i) (t n (i + 1)) ω) ^ 2 ∂μ)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω,
      (∑ i ∈ s n, H n i ω * squareError M A (t n i) (t n (i + 1)) ω) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => sq_nonneg _))
    (fun n => integral_grid_weighted_error_sq_le hM hQ hM2 (t n) (ht n) (H n)
      (hH n) (hD4 n) (hA2 n) hK (hbound n) (s n))
  simpa only [mul_zero] using hsmall.const_mul (2 * K ^ 2)

end Problem367.MartingaleQuadraticVariation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_CompensatorVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal

namespace Problem367.CompensatorVariation

theorem squaredIncrements_nonneg (a : ℕ → ℝ) (N : ℕ) :
    0 ≤ squaredIncrements a N := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem squaredIncrements_le {a : ℕ → ℝ} {N : ℕ} {δ : ℝ}
    (hpos : ∀ i < N, 0 ≤ a (i + 1) - a i)
    (hsmall : ∀ i < N, a (i + 1) - a i ≤ δ) :
    squaredIncrements a N ≤ δ * (a N - a 0) := by
  calc
    squaredIncrements a N ≤ ∑ i ∈ Finset.range N, δ * (a (i + 1) - a i) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right (hsmall i (Finset.mem_range.mp hi))
        (hpos i (Finset.mem_range.mp hi))
    _ = δ * (a N - a 0) := by rw [← Finset.mul_sum, Finset.sum_range_sub]

theorem squaredIncrements_le_total_sq {a : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ i < N, 0 ≤ a (i + 1) - a i) :
    squaredIncrements a N ≤ (a N - a 0) ^ 2 := by
  have h := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.range N) (fun i hi => hpos i (Finset.mem_range.mp hi))
  simpa only [squaredIncrements, Finset.sum_range_sub] using h

theorem total_nonneg {a : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ i < N, 0 ≤ a (i + 1) - a i) : 0 ≤ a N - a 0 := by
  rw [← Finset.sum_range_sub a N]
  exact Finset.sum_nonneg (fun i hi => hpos i (Finset.mem_range.mp hi))

theorem increment_le_total {a : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ i < N, 0 ≤ a (i + 1) - a i) {i : ℕ} (hi : i < N) :
    a (i + 1) - a i ≤ a N - a 0 := by
  rw [← Finset.sum_range_sub a N]
  exact Finset.single_le_sum (fun j hj => hpos j (Finset.mem_range.mp hj))
    (Finset.mem_range.mpr hi)

theorem tendsto_squaredIncrements {I : Type*} [PseudoMetricSpace I]
    {K : Set I} (hK : IsCompact K) {A : I → ℝ} (hA : ContinuousOn A K)
    (t : ℕ → ℕ → I) (N : ℕ → ℕ) (mesh : ℕ → ℝ)
    (hmem : ∀ n i, i ≤ N n → t n i ∈ K)
    (hdist : ∀ n i, i < N n → dist (t n i) (t n (i + 1)) ≤ mesh n)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n i, i < N n → 0 ≤ A (t n (i + 1)) - A (t n i))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ n, A (t n (N n)) - A (t n 0) ≤ C) :
    Tendsto (fun n => squaredIncrements (fun i => A (t n i)) (N n)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε / (C + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hA) η hη
  obtain ⟨n₀, hn₀⟩ := (hmesh.eventually (gt_mem_nhds hδ)).exists_forall_of_atTop
  refine ⟨n₀, ?_⟩
  intro n hn
  have hsmall (i : ℕ) (hi : i < N n) : A (t n (i + 1)) - A (t n i) ≤ η := by
    have hh := hmod (t n (i + 1)) (hmem n (i + 1) (Nat.succ_le_of_lt hi))
      (t n i) (hmem n i hi.le) (by
        rw [dist_comm]
        exact (hdist n i hi).trans_lt (hn₀ n hn))
    exact (le_abs_self _).trans (by simpa only [Real.dist_eq] using hh.le)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (squaredIncrements_nonneg _ _)]
  calc
    squaredIncrements (fun i => A (t n i)) (N n) ≤
        η * (A (t n (N n)) - A (t n 0)) := squaredIncrements_le (hpos n) hsmall
    _ ≤ η * C := mul_le_mul_of_nonneg_left (hbound n) hη.le
    _ < ε := by
      change ε / (C + 1) * C < ε
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ (by linarith : 0 < C + 1)).2
      nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem memLp_increment_of_total_bound [IsFiniteMeasure μ]
    {a : ℕ → Ω → ℝ} (hmeas : ∀ i, AEStronglyMeasurable (a i) μ) {N : ℕ}
    (hpos : ∀ᵐ ω ∂μ, ∀ i < N, 0 ≤ a (i + 1) ω - a i ω)
    {C : ℝ} (hbound : ∀ᵐ ω ∂μ, a N ω - a 0 ω ≤ C)
    {i : ℕ} (hi : i < N) (p : ℝ≥0∞) :
    MemLp (fun ω => a (i + 1) ω - a i ω) p μ := by
  apply MemLp.of_bound ((hmeas _).sub (hmeas _)) C
  filter_upwards [hpos, hbound] with ω hp hb
  rw [Real.norm_eq_abs, Pi.sub_apply, abs_of_nonneg (hp i hi)]
  exact (increment_le_total (a := fun j => a j ω) hp hi).trans hb

theorem tendsto_integral_squaredIncrements [IsFiniteMeasure μ]
    {I : Type*} [PseudoMetricSpace I] {K : Set I} (hK : IsCompact K)
    {A : I → Ω → ℝ} (hmeas : ∀ t, AEStronglyMeasurable (A t) μ)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => A t ω) K)
    (t : ℕ → ℕ → I) (N : ℕ → ℕ) (mesh : ℕ → ℝ)
    (hmem : ∀ n i, i ≤ N n → t n i ∈ K)
    (hdist : ∀ n i, i < N n → dist (t n i) (t n (i + 1)) ≤ mesh n)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ᵐ ω ∂μ, ∀ n i, i < N n → 0 ≤ A (t n (i + 1)) ω - A (t n i) ω)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ ω ∂μ, ∀ n, A (t n (N n)) ω - A (t n 0) ω ≤ C) :
    Tendsto (fun n => ∫ ω, squaredIncrements (fun i => A (t n i) ω) (N n) ∂μ)
      atTop (𝓝 0) := by
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun ω => squaredIncrements (fun i => A (t n i) ω) (N n)) μ := by
    convert (Finset.aestronglyMeasurable_sum (Finset.range (N n))
      (fun i _ => ((hmeas (t n (i + 1))).sub (hmeas (t n i))).pow 2)) using 1
    all_goals try with_reducible_and_instances rfl
    ext ω
    simp only [squaredIncrements, Finset.sum_apply, Pi.pow_apply, Pi.sub_apply]
  have hh := tendsto_integral_of_dominated_convergence
    (μ := μ) (F := fun n ω => squaredIncrements (fun i => A (t n i) ω) (N n))
    (f := fun _ => (0 : ℝ)) (fun _ => C ^ 2) hm (integrable_const _) ?_ ?_
  · simpa only [integral_zero] using hh
  · intro n
    filter_upwards [hpos, hbound] with ω hp hb
    rw [Real.norm_eq_abs, abs_of_nonneg (squaredIncrements_nonneg _ _)]
    exact (squaredIncrements_le_total_sq (hp n)).trans
      ((sq_le_sq₀ (total_nonneg (a := fun i => A (t n i) ω) (hp n)) hC).2 (hb n))
  · filter_upwards [hc, hpos, hbound] with ω hω hp hb
    exact tendsto_squaredIncrements hK hω t N mesh hmem hdist hmesh hp hC hb

theorem tendsto_sum_integral_sq_increments [IsFiniteMeasure μ]
    {I : Type*} [PseudoMetricSpace I] {K : Set I} (hK : IsCompact K)
    {A : I → Ω → ℝ} (hmeas : ∀ t, AEStronglyMeasurable (A t) μ)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => A t ω) K)
    (t : ℕ → ℕ → I) (N : ℕ → ℕ) (mesh : ℕ → ℝ)
    (hmem : ∀ n i, i ≤ N n → t n i ∈ K)
    (hdist : ∀ n i, i < N n → dist (t n i) (t n (i + 1)) ≤ mesh n)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ᵐ ω ∂μ, ∀ n i, i < N n → 0 ≤ A (t n (i + 1)) ω - A (t n i) ω)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ ω ∂μ, ∀ n, A (t n (N n)) ω - A (t n 0) ω ≤ C) :
    Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      ∫ ω, (A (t n (i + 1)) ω - A (t n i) ω) ^ 2 ∂μ) atTop (𝓝 0) := by
  have heq (n : ℕ) : (∑ i ∈ Finset.range (N n),
      ∫ ω, (A (t n (i + 1)) ω - A (t n i) ω) ^ 2 ∂μ) =
      ∫ ω, squaredIncrements (fun i => A (t n i) ω) (N n) ∂μ := by
    symm
    apply integral_finsetSum
    intro i hi
    apply (memLp_increment_of_total_bound (fun j => hmeas (t n j))
      (hpos.mono (fun ω hω => hω n))
      (hbound.mono (fun ω hω => hω n)) (Finset.mem_range.mp hi) 2).integrable_sq
  simp_rw [heq]
  exact tendsto_integral_squaredIncrements hK hmeas hc t N mesh hmem hdist hmesh hpos hC hbound

end Problem367.CompensatorVariation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_ArtanhMartingaleFormula
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Problem367.ArtanhMartingaleFormula

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

lemma firstWeight_bound {r x : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (hx : |x| ≤ r) :
    |firstWeight x| ≤ 1 / (1 - r ^ 2) := by
  have hsq : x ^ 2 ≤ r ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg x) hr0).2 hx
  have hd : 0 < 1 - r ^ 2 := by nlinarith
  have hdx : 0 < 1 - x ^ 2 := by linarith
  rw [firstWeight, abs_of_pos (div_pos zero_lt_one hdx)]
  exact one_div_le_one_div_of_le hd (by linarith)

lemma secondWeight_bound {r x : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (hx : |x| ≤ r) :
    |secondWeight x| ≤ r / (1 - r ^ 2) ^ 2 := by
  have hsq : x ^ 2 ≤ r ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg x) hr0).2 hx
  have hd : 0 < 1 - r ^ 2 := by nlinarith
  simp only [secondWeight, abs_div, abs_pow, sq_abs]
  calc
    |x| / (1 - x ^ 2) ^ 2 ≤ r / (1 - x ^ 2) ^ 2 := by gcongr
    _ ≤ r / (1 - r ^ 2) ^ 2 := by gcongr

omit mΩ in
lemma stronglyMeasurable_firstWeight {m : MeasurableSpace Ω} {X : Ω → ℝ}
    (hX : StronglyMeasurable[m] X) :
    StronglyMeasurable[m] (fun ω => firstWeight (X ω)) :=
  stronglyMeasurable_const.div (stronglyMeasurable_const.sub (hX.pow 2))

omit mΩ in
lemma stronglyMeasurable_secondWeight {m : MeasurableSpace Ω} {X : Ω → ℝ}
    (hX : StronglyMeasurable[m] X) :
    StronglyMeasurable[m] (fun ω => secondWeight (X ω)) :=
  hX.div ((stronglyMeasurable_const.sub (hX.pow 2)).pow 2)

theorem tendsto_integral_abs_zero_of_sq [IsProbabilityMeasure μ]
    (E : ℕ → Ω → ℝ) (hE : ∀ n, MemLp (E n) 2 μ)
    (hlim : Tendsto (fun n => ∫ ω, E n ω ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, |E n ω| ∂μ) atTop (𝓝 0) := by
  refine squeeze_zero (fun n => integral_nonneg (fun ω => abs_nonneg _))
    (fun n => integral_abs_le_sqrt_integral_sq (hE n).aestronglyMeasurable.aemeasurable
      (hE n).integrable_sq) ?_
  simpa only [Function.comp_def, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hlim

omit mΩ in
theorem taylor_identity {I : Type*} (M : I → Ω → ℝ) (t : ℕ → I) (N : ℕ) (ω : Ω) :
    (∑ i ∈ Finset.range N, ArtanhTaylor.remainder (M (t i) ω) (M (t (i + 1)) ω)) =
      Real.artanh (M (t N) ω) - Real.artanh (M (t 0) ω) -
        linearSum M t N ω - quadraticSum M t N ω := by
  have hfirst : (∑ i ∈ Finset.range N,
      (M (t (i + 1)) ω - M (t i) ω) / (1 - M (t i) ω ^ 2)) = linearSum M t N ω := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [firstWeight, div_eq_mul_inv]
    ring
  have hsecond : (∑ i ∈ Finset.range N,
      M (t i) ω * (M (t (i + 1)) ω - M (t i) ω) ^ 2 / (1 - M (t i) ω ^ 2) ^ 2) =
      quadraticSum M t N ω := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [secondWeight, div_eq_mul_inv]
    ring
  rw [ArtanhTaylor.sum_remainder, hfirst, hsecond]

omit mΩ in
theorem quadratic_sub_compensator {I : Type*} (M A : I → Ω → ℝ)
    (t : ℕ → I) (N : ℕ) (ω : Ω) :
    quadraticSum M t N ω - compensatorSum M A t N ω =
      ∑ i ∈ Finset.range N, secondWeight (M (t i) ω) *
        MartingaleQuadraticVariation.squareError M A (t i) (t (i + 1)) ω := by
  rw [quadraticSum, compensatorSum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [MartingaleQuadraticVariation.squareError, MartingaleQuadraticVariation.increment]
  ring

lemma tendsto_L1_of_intermediate {U V : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hU : ∀ n, Integrable (U n) μ) (hV : ∀ n, Integrable (V n) μ)
    (hY : Integrable Y μ)
    (huv : Tendsto (fun n => ∫ ω, |U n ω - V n ω| ∂μ) atTop (𝓝 0))
    (hvy : Tendsto (fun n => ∫ ω, |V n ω - Y ω| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, |U n ω - Y ω| ∂μ) atTop (𝓝 0) := by
  have hlim := huv.add hvy
  simp only [zero_add] at hlim
  refine squeeze_zero (fun n => integral_nonneg (fun _ => abs_nonneg _)) (fun n => ?_) hlim
  have h1 : Integrable (fun ω => |U n ω - V n ω|) μ := ((hU n).sub (hV n)).abs
  have h2 : Integrable (fun ω => |V n ω - Y ω|) μ := ((hV n).sub hY).abs
  calc
    _ ≤ ∫ ω, |U n ω - V n ω| + |V n ω - Y ω| ∂μ := by
      apply integral_mono ((hU n).sub hY).abs (h1.add h2)
      intro ω
      simpa only [Pi.sub_apply, Pi.add_apply] using abs_sub_le (U n ω) (V n ω) (Y ω)
    _ = _ := integral_add h1 h2

theorem artanh_eq_of_cubic_and_compensated_limits [IsProbabilityMeasure μ]
    {I : Type*} [Preorder I] {F : Filtration I mΩ} {M A : I → Ω → ℝ}
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ)
    (t : ℕ → ℕ → I) (ht : ∀ n, Monotone (t n)) (N : ℕ → ℕ)
    {s T : I} (hstart : ∀ n, t n 0 = s) (hend : ∀ n, t n (N n) = T)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hbound : ∀ u, ∀ᵐ ω ∂μ, |M u ω| ≤ r)
    (hD4 : ∀ n i, MemLp (fun ω => (M (t n (i + 1)) ω - M (t n i) ω) ^ 2) 2 μ)
    (hA2 : ∀ n i, MemLp (fun ω => A (t n (i + 1)) ω - A (t n i) ω) 2 μ)
    (hsmall : Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      ((∫ ω, (M (t n (i + 1)) ω - M (t n i) ω) ^ 4 ∂μ) +
        ∫ ω, (A (t n (i + 1)) ω - A (t n i) ω) ^ 2 ∂μ)) atTop (𝓝 0))
    (hthird : Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      ∫ ω, |M (t n (i + 1)) ω - M (t n i) ω| ^ 3 ∂μ) atTop (𝓝 0))
    {L V : Ω → ℝ} (hL : Integrable L μ) (hV : Integrable V μ)
    (hlinear : Tendsto (fun n => ∫ ω, |linearSum M (t n) (N n) ω - L ω| ∂μ)
      atTop (𝓝 0))
    (hcompensator : Tendsto (fun n => ∫ ω,
      |compensatorSum M A (t n) (N n) ω - V ω| ∂μ) atTop (𝓝 0)) :
    (fun ω => Real.artanh (M T ω) - Real.artanh (M s ω)) =ᵐ[μ]
      fun ω => L ω + V ω := by
  have hden : 0 < 1 - r ^ 2 := by nlinarith
  have hfirst (n i : ℕ) : StronglyMeasurable[F (t n i)]
      (fun ω => firstWeight (M (t n i) ω)) :=
    stronglyMeasurable_firstWeight (hM.stronglyMeasurable _)
  have hsecond (n i : ℕ) : StronglyMeasurable[F (t n i)]
      (fun ω => secondWeight (M (t n i) ω)) :=
    stronglyMeasurable_secondWeight (hM.stronglyMeasurable _)
  have hbfirst (n i : ℕ) : ∀ᵐ ω ∂μ,
      |firstWeight (M (t n i) ω)| ≤ 1 / (1 - r ^ 2) :=
    (hbound _).mono (fun ω hω => firstWeight_bound hr0 hr hω)
  have hbsecond (n i : ℕ) : ∀ᵐ ω ∂μ,
      |secondWeight (M (t n i) ω)| ≤ r / (1 - r ^ 2) ^ 2 :=
    (hbound _).mono (fun ω hω => secondWeight_bound hr0 hr hω)
  have hfirstTop (n i : ℕ) : MemLp (fun ω => firstWeight (M (t n i) ω)) ⊤ μ :=
    memLp_top_of_bound ((hfirst n i).mono (F.le _)).aestronglyMeasurable _
      (by simpa only [Real.norm_eq_abs] using hbfirst n i)
  have hsecondTop (n i : ℕ) : MemLp (fun ω => secondWeight (M (t n i) ω)) ⊤ μ :=
    memLp_top_of_bound ((hsecond n i).mono (F.le _)).aestronglyMeasurable _
      (by simpa only [Real.norm_eq_abs] using hbsecond n i)
  have hLin2 (n : ℕ) : MemLp (linearSum M (t n) (N n)) 2 μ :=
    memLp_finsetSum _ (fun i _ => MeasureTheory.MemLp.mul' (hφ := (hfirstTop n i)) (hf := ((hM2 _).sub (hM2 _))))
  have hQuad2 (n : ℕ) : MemLp (quadraticSum M (t n) (N n)) 2 μ :=
    memLp_finsetSum _ (fun i _ => MeasureTheory.MemLp.mul' (hφ := (hsecondTop n i)) (hf := (hD4 n i)))
  have hComp2 (n : ℕ) : MemLp (compensatorSum M A (t n) (N n)) 2 μ :=
    memLp_finsetSum _ (fun i _ => MeasureTheory.MemLp.mul' (hφ := (hsecondTop n i)) (hf := (hA2 n i)))
  have hErrSq : Tendsto (fun n => ∫ ω,
      (quadraticSum M (t n) (N n) ω - compensatorSum M A (t n) (N n) ω) ^ 2 ∂μ)
      atTop (𝓝 0) := by
    have hh := MartingaleQuadraticVariation.tendsto_integral_grid_weighted_error_sq
      hM hQ hM2 t ht (fun n i ω => secondWeight (M (t n i) ω)) hsecond hD4 hA2
      (by positivity : 0 ≤ r / (1 - r ^ 2) ^ 2) hbsecond
      (fun n => Finset.range (N n)) hsmall
    simpa only [quadratic_sub_compensator] using hh
  have hErr := tendsto_integral_abs_zero_of_sq
    (fun n ω => quadraticSum M (t n) (N n) ω - compensatorSum M A (t n) (N n) ω)
    (fun n => (hQuad2 n).sub (hComp2 n)) hErrSq
  have hQuadLimit := tendsto_L1_of_intermediate
    (fun n => (hQuad2 n).integrable (by norm_num))
    (fun n => (hComp2 n).integrable (by norm_num)) hV hErr hcompensator
  have hm (n i : ℕ) : Measurable (M (t n i)) :=
    ((hM.stronglyMeasurable _).mono (F.le _)).measurable
  have hloc (n : ℕ) : ∀ᵐ ω ∂μ, ∀ i ≤ N n, |M (t n i) ω| ≤ r := by
    filter_upwards [ae_all_iff.2 (fun i => hbound (t n i))] with ω hω
    exact fun i _ => hω i
  have hcube (n i : ℕ) : Integrable (fun ω => |M (t n (i + 1)) ω - M (t n i) ω| ^ 3) μ :=
    ArtanhTaylor.integrable_cube_of_localized (hm n i) (hm n (i + 1)) (hbound _) (hbound _)
  have hRint (n : ℕ) := (ArtanhTaylor.integrable_sum_remainder_and_bound hr
    (fun i => M (t n i)) (N n) (hm n) (hloc n) (fun i _ => hcube n i)).1
  have hRlim := ArtanhTaylor.tendsto_integral_abs_sum_remainder hr
    (fun n i => M (t n i)) N hm hloc hthird
  have hY : Integrable (fun ω => Real.artanh (M T ω) - Real.artanh (M s ω)) μ := by
    have hi := ((hRint 0).add ((hLin2 0).integrable (by norm_num))).add
      ((hQuad2 0).integrable (by norm_num))
    apply hi.congr
    filter_upwards [] with ω
    have he := taylor_identity M (t 0) (N 0) ω
    rw [hstart 0, hend 0] at he
    simp only [Pi.add_apply]
    linarith
  apply MartingaleTaylorRemainder.ae_eq_add_of_taylor_L1_limits hY hL hV
    (fun n => (hLin2 n).integrable (by norm_num))
    (fun n => (hQuad2 n).integrable (by norm_num)) _ hlinear hQuadLimit
  simpa only [taylor_identity, hstart, hend] using hRlim

theorem integral_grid_square_sum_le [IsProbabilityMeasure μ]
    {I : Type*} [Preorder I] {F : Filtration I mΩ} {M : I → Ω → ℝ}
    (hM : Martingale M F μ) (hM2 : ∀ u, MemLp (M u) 2 μ)
    (t : ℕ → I) (ht : Monotone t) (N : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (hbound : ∀ᵐ ω ∂μ, |M (t N) ω| ≤ r) :
    (∫ ω, ∑ i ∈ Finset.range N, (M (t (i + 1)) ω - M (t i) ω) ^ 2 ∂μ) ≤ r ^ 2 := by
  let G : Filtration ℕ mΩ :=
    ⟨fun i => F (t i), fun _ _ hij => F.mono (ht hij), fun i => F.le (t i)⟩
  have hMG : Martingale (fun i => M (t i)) G μ :=
    ⟨fun i => hM.stronglyMeasurable _, fun _ _ hij => hM.condExp_ae_eq (ht hij)⟩
  calc
    _ = ∑ i ∈ Finset.range N, ∫ ω, (M (t (i + 1)) ω - M (t i) ω) ^ 2 ∂μ :=
      integral_finsetSum _ (fun i _ => ((hM2 _).sub (hM2 _)).integrable_sq)
    _ = ∫ ω, (M (t N) ω - M (t 0) ω) ^ 2 ∂μ :=
      MartingaleTransformL2.sum_integral_sq_increment hMG (fun i => hM2 _) N
    _ ≤ ∫ ω, M (t N) ω ^ 2 ∂μ :=
      MartingaleTransformL2.integral_sq_increment_le hM (ht (Nat.zero_le N)) (hM2 _) (hM2 _)
    _ ≤ ∫ _ : Ω, r ^ 2 ∂μ := by
      apply integral_mono_ae (hM2 _).integrable_sq (integrable_const _)
      filter_upwards [hbound] with ω hω
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hr).2 hω
    _ = r ^ 2 := by simp

theorem artanh_eq_of_compensated_sum_limits [IsProbabilityMeasure μ]
    {I : Type*} [Preorder I] {F : Filtration I mΩ} {M A : I → Ω → ℝ}
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (t : ℕ → ℕ → I) (ht : ∀ n, Monotone (t n)) (N : ℕ → ℕ)
    {s T : I} (hstart : ∀ n, t n 0 = s) (hend : ∀ n, t n (N n) = T)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hbound : ∀ u, ∀ᵐ ω ∂μ, |M u ω| ≤ r)
    (hA2 : ∀ n i, MemLp (fun ω => A (t n (i + 1)) ω - A (t n i) ω) 2 μ)
    (hsmall : Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      ((∫ ω, (M (t n (i + 1)) ω - M (t n i) ω) ^ 4 ∂μ) +
        ∫ ω, (A (t n (i + 1)) ω - A (t n i) ω) ^ 2 ∂μ)) atTop (𝓝 0))
    {L V : Ω → ℝ} (hL : Integrable L μ) (hV : Integrable V μ)
    (hlinear : Tendsto (fun n => ∫ ω, |linearSum M (t n) (N n) ω - L ω| ∂μ)
      atTop (𝓝 0))
    (hcompensator : Tendsto (fun n => ∫ ω,
      |compensatorSum M A (t n) (N n) ω - V ω| ∂μ) atTop (𝓝 0)) :
    (fun ω => Real.artanh (M T ω) - Real.artanh (M s ω)) =ᵐ[μ]
      fun ω => L ω + V ω := by
  have hm (u : I) : StronglyMeasurable (M u) := (hM.stronglyMeasurable u).mono (F.le u)
  have hM2 (u : I) : MemLp (M u) 2 μ :=
    MemLp.of_bound (hm u).aestronglyMeasurable r
      (by simpa only [Real.norm_eq_abs] using hbound u)
  have hD4 (n i : ℕ) : MemLp (fun ω => (M (t n (i + 1)) ω - M (t n i) ω) ^ 2) 2 μ := by
    apply MemLp.of_bound (((hm _).sub (hm _)).pow 2).aestronglyMeasurable ((2 * r) ^ 2)
    filter_upwards [hbound (t n i), hbound (t n (i + 1))] with ω hs ht
    have hd : |M (t n (i + 1)) ω - M (t n i) ω| ≤ 2 * r :=
      (abs_sub _ _).trans (by linarith)
    simpa only [Pi.pow_apply, Pi.sub_apply, Real.norm_eq_abs, abs_pow, sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * r)).2 hd
  have h4 (n i : ℕ) : Integrable (fun ω => (M (t n (i + 1)) ω - M (t n i) ω) ^ 4) μ := by
    simpa only [← pow_mul] using (hD4 n i).integrable_sq
  have hfourth : Tendsto (fun n => ∫ ω, ∑ i ∈ Finset.range (N n),
      (M (t n (i + 1)) ω - M (t n i) ω) ^ 4 ∂μ) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => integral_nonneg (fun ω => Finset.sum_nonneg
      (fun i _ => by positivity))) (fun n => ?_) hsmall
    rw [integral_finsetSum _ (fun i _ => h4 n i)]
    apply Finset.sum_le_sum
    intro i _
    exact le_add_of_nonneg_right (integral_nonneg (fun ω => sq_nonneg _))
  have hthirdInt := MartingaleTaylorRemainder.tendsto_integral_sum_abs_cube_zero
    (fun n => Finset.range (N n))
    (fun n i ω => M (t n (i + 1)) ω - M (t n i) ω)
    (fun n i _ => ((hm _).sub (hm _)).aestronglyMeasurable)
    (fun n i _ => ((hM2 _).sub (hM2 _)).integrable_sq)
    (fun n i _ => h4 n i) (sq_nonneg r)
    (fun n => integral_grid_square_sum_le hM hM2 (t n) (ht n) (N n) hr0 (hbound _)) hfourth
  have hthird : Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      ∫ ω, |M (t n (i + 1)) ω - M (t n i) ω| ^ 3 ∂μ) atTop (𝓝 0) := by
    have he (n : ℕ) : (∫ ω, ∑ i ∈ Finset.range (N n),
        |M (t n (i + 1)) ω - M (t n i) ω| ^ 3 ∂μ) =
        ∑ i ∈ Finset.range (N n), ∫ ω, |M (t n (i + 1)) ω - M (t n i) ω| ^ 3 ∂μ :=
      integral_finsetSum _ (fun i _ => ArtanhTaylor.integrable_cube_of_localized
        (hm _).measurable (hm _).measurable (hbound _) (hbound _))
    simpa only [he] using hthirdInt
  exact artanh_eq_of_cubic_and_compensated_limits hM hQ hM2 t ht N hstart hend
    hr0 hr hbound hD4 hA2 hsmall hthird hL hV hlinear hcompensator

theorem artanh_eq_of_continuous_compensated_limits [IsProbabilityMeasure μ]
    {I : Type*} [Preorder I] [PseudoMetricSpace I]
    {F : Filtration I mΩ} {M A : I → Ω → ℝ}
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (t : ℕ → ℕ → I) (ht : ∀ n, Monotone (t n)) (N : ℕ → ℕ)
    {s T : I} (hstart : ∀ n, t n 0 = s) (hend : ∀ n, t n (N n) = T)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hbound : ∀ u, ∀ᵐ ω ∂μ, |M u ω| ≤ r)
    {K : Set I} (hK : IsCompact K)
    (hcM : ∀ᵐ ω ∂μ, ContinuousOn (fun u => M u ω) K)
    (hcA : ∀ᵐ ω ∂μ, ContinuousOn (fun u => A u ω) K)
    (hmem : ∀ n i, i ≤ N n → t n i ∈ K)
    (mesh : ℕ → ℝ) (hmesh : Tendsto mesh atTop (𝓝 0))
    (hdist : ∀ n i, i < N n → dist (t n i) (t n (i + 1)) ≤ mesh n)
    (hpos : ∀ᵐ ω ∂μ, ∀ n i, i < N n → 0 ≤ A (t n (i + 1)) ω - A (t n i) ω)
    {C : ℝ} (hC : 0 ≤ C)
    (htotal : ∀ᵐ ω ∂μ, ∀ n, A (t n (N n)) ω - A (t n 0) ω ≤ C)
    {L V : Ω → ℝ} (hL : Integrable L μ) (hV : Integrable V μ)
    (hlinear : Tendsto (fun n => ∫ ω, |linearSum M (t n) (N n) ω - L ω| ∂μ)
      atTop (𝓝 0))
    (hcompensator : Tendsto (fun n => ∫ ω,
      |compensatorSum M A (t n) (N n) ω - V ω| ∂μ) atTop (𝓝 0)) :
    (fun ω => Real.artanh (M T ω) - Real.artanh (M s ω)) =ᵐ[μ]
      fun ω => L ω + V ω := by
  have hfour := BoundedMartingaleVariation.tendsto_sum_integral_fourth_of_continuous
    hM hr0 hbound hK hcM t ht N hmem mesh hmesh
    (fun n i hi => by simpa only [dist_comm] using hdist n i hi)
  have hAm (u : I) : AEStronglyMeasurable (A u) μ :=
    ((MartingaleQuadraticVariation.stronglyAdapted_compensator hM hQ u).mono
      (F.le u)).aestronglyMeasurable
  have hcomp := CompensatorVariation.tendsto_sum_integral_sq_increments hK hAm hcA
    t N mesh hmem hdist hmesh hpos hC htotal
  have hsmall : Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      ((∫ ω, (M (t n (i + 1)) ω - M (t n i) ω) ^ 4 ∂μ) +
        ∫ ω, (A (t n (i + 1)) ω - A (t n i) ω) ^ 2 ∂μ)) atTop (𝓝 0) := by
    simpa only [Finset.sum_add_distrib, zero_add] using hfour.add hcomp
  let u : ℕ → ℕ → I := fun n i => t n (min i (N n))
  have hu (n i : ℕ) (hi : i ≤ N n) : u n i = t n i := by simp only [u, min_eq_left hi]
  have huend (n i : ℕ) (hi : N n ≤ i) : u n i = t n (N n) := by simp only [u, min_eq_right hi]
  have humo (n : ℕ) : Monotone (u n) :=
    fun i j hij => ht n (min_le_min_right (N n) hij)
  have hustart (n : ℕ) : u n 0 = s := by rw [hu n 0 (Nat.zero_le _), hstart]
  have huendT (n : ℕ) : u n (N n) = T := by rw [hu n (N n) le_rfl, hend]
  have hA2 (n i : ℕ) : MemLp (fun ω => A (u n (i + 1)) ω - A (u n i) ω) 2 μ := by
    by_cases hi : i < N n
    · rw [hu n i hi.le, hu n (i + 1) hi]
      exact CompensatorVariation.memLp_increment_of_total_bound (fun j => hAm (t n j))
        (hpos.mono (fun ω hω => hω n)) (htotal.mono (fun ω hω => hω n)) hi 2
    · have hNi := Nat.le_of_not_gt hi
      simp only [huend n i hNi, huend n (i + 1) (hNi.trans (Nat.le_succ i)), sub_self]
      exact MemLp.zero
  have henergy (n : ℕ) : (∑ i ∈ Finset.range (N n),
      ((∫ ω, (M (u n (i + 1)) ω - M (u n i) ω) ^ 4 ∂μ) +
        ∫ ω, (A (u n (i + 1)) ω - A (u n i) ω) ^ 2 ∂μ)) =
      ∑ i ∈ Finset.range (N n),
      ((∫ ω, (M (t n (i + 1)) ω - M (t n i) ω) ^ 4 ∂μ) +
        ∫ ω, (A (t n (i + 1)) ω - A (t n i) ω) ^ 2 ∂μ) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [hu n i hi'.le, hu n (i + 1) hi']
  have hlinEq (n : ℕ) (ω : Ω) : linearSum M (u n) (N n) ω = linearSum M (t n) (N n) ω := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [hu n i hi'.le, hu n (i + 1) hi']
  have hcompEq (n : ℕ) (ω : Ω) :
      compensatorSum M A (u n) (N n) ω = compensatorSum M A (t n) (N n) ω := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [hu n i hi'.le, hu n (i + 1) hi']
  exact artanh_eq_of_compensated_sum_limits hM hQ u humo N hustart huendT hr0 hr hbound hA2
    (by simpa only [henergy] using hsmall) hL hV
    (by simpa only [hlinEq] using hlinear) (by simpa only [hcompEq] using hcompensator)

theorem artanh_eq_stochasticLimit_add_integral [IsProbabilityMeasure μ]
    {F : Filtration ℝ mΩ} {M A a : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (hMm : Measurable (fun p : ℝ × Ω => M p.1 p.2))
    (hcM : ∀ᵐ ω ∂μ, ContinuousOn (fun t => M t ω) (Set.Icc 0 T))
    (hcA : ∀ᵐ ω ∂μ, ContinuousOn (fun t => A t ω) (Set.Icc 0 T))
    (hmonoA : ∀ᵐ ω ∂μ, MonotoneOn (fun t => A t ω) (Set.Icc 0 T))
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hbound : ∀ᵐ ω ∂μ, ∀ t, |M t ω| ≤ r)
    {C : ℝ} (hC : 0 ≤ C) (htotal : ∀ᵐ ω ∂μ, A T ω - A 0 ω ≤ C)
    (ha : Integrable (fun p : ℝ × Ω => a p.1 p.2)
      ((volume.restrict (Set.Ioc 0 T)).prod μ))
    (hprimitive : ∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc 0 T,
      A t ω = A 0 ω + ∫ s in (0 : ℝ)..t, a s ω)
    {L : Ω → ℝ} (hL : Integrable L μ)
    (hlinear : Tendsto (fun n => ∫ ω,
      |linearSum M (EnergyRiemann.point T (n + 1)) (n + 1) ω - L ω| ∂μ)
      atTop (𝓝 0)) :
    (fun ω => Real.artanh (M T ω) - Real.artanh (M 0 ω)) =ᵐ[μ]
      fun ω => L ω + ∫ t in (0 : ℝ)..T, secondWeight (M t ω) * a t ω := by
  let f : ℝ → Ω → ℝ := fun t ω => secondWeight (M t ω)
  have hden : 0 < 1 - r ^ 2 := by nlinarith
  have hfm : Measurable (fun p : ℝ × Ω => f p.1 p.2) := by
    unfold f secondWeight
    exact hMm.div ((measurable_const.sub (hMm.pow_const 2)).pow_const 2)
  have hfc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => f t ω) (Set.Icc 0 T) := by
    filter_upwards [hcM, hbound] with ω hc hb
    apply hc.div ((continuousOn_const.sub (hc.pow 2)).pow 2)
    intro t ht
    have hs : M t ω ^ 2 ≤ r ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hr0).2 (hb t)
    exact pow_ne_zero 2 (by linarith : 1 - M t ω ^ 2 ≠ 0)
  have hfb : ∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc 0 T, |f t ω| ≤ r / (1 - r ^ 2) ^ 2 :=
    hbound.mono (fun ω hω t _ => secondWeight_bound hr0 hr (hω t))
  have hcompLimit := WeightedPrimitiveApproximation.tendsto_integral_abs_compensator_error
    hT (by positivity : 0 ≤ r / (1 - r ^ 2) ^ 2) hfm hfc ha hfb hprimitive
  have hshift := hcompLimit.comp (tendsto_add_atTop_nat 1)
  have hV : Integrable (fun ω => ∫ t in (0 : ℝ)..T, f t ω * a t ω) μ := by
    simpa only [intervalIntegral.integral_of_le hT] using
      (WeightedPrimitiveApproximation.integrable_weightedDensity hfm ha hfb).integral_prod_right
  have hmesh : Tendsto (fun n : ℕ => T / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hmem (n i : ℕ) (hi : i ≤ n + 1) : EnergyRiemann.point T (n + 1) i ∈ Set.Icc 0 T :=
    EnergyRiemann.point_mem hT (Nat.succ_pos n) hi
  have hdist (n i : ℕ) (_hi : i < n + 1) :
      dist (EnergyRiemann.point T (n + 1) i) (EnergyRiemann.point T (n + 1) (i + 1)) ≤
        T / ((n + 1 : ℕ) : ℝ) := by
    rw [dist_comm, Real.dist_eq, EnergyRiemann.point_step, abs_of_nonneg (by positivity)]
  have hpos : ∀ᵐ ω ∂μ, ∀ n i, i < n + 1 →
      0 ≤ A (EnergyRiemann.point T (n + 1) (i + 1)) ω - A (EnergyRiemann.point T (n + 1) i) ω := by
    filter_upwards [hmonoA] with ω hω
    intro n i hi
    exact sub_nonneg.mpr (hω (hmem n i hi.le) (hmem n (i + 1) hi)
      (EnergyRiemann.point_mono hT (n + 1) (Nat.le_succ i)))
  have htotal' : ∀ᵐ ω ∂μ, ∀ n,
      A (EnergyRiemann.point T (n + 1) (n + 1)) ω - A (EnergyRiemann.point T (n + 1) 0) ω ≤ C := by
    filter_upwards [htotal] with ω hω
    intro n
    simpa only [EnergyRiemann.point_zero, EnergyRiemann.point_end T (Nat.succ_pos n)] using hω
  apply artanh_eq_of_continuous_compensated_limits hM hQ
    (fun n => EnergyRiemann.point T (n + 1)) (fun n => EnergyRiemann.point_mono hT (n + 1))
    (fun n => n + 1) (fun n => EnergyRiemann.point_zero T (n + 1))
    (fun n => EnergyRiemann.point_end T (Nat.succ_pos n)) hr0 hr
    (fun t => hbound.mono (fun ω hω => hω t)) isCompact_Icc hcM hcA hmem
    (fun n => T / ((n + 1 : ℕ) : ℝ)) hmesh hdist hpos hC htotal' hL hV hlinear
  simpa only [Function.comp_def, compensatorSum, f] using hshift

end Problem367.ArtanhMartingaleFormula

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_NNRealArtanhFormula
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology

namespace Problem367.NNRealArtanhFormula

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

lemma martingale_realExtension {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ) :
    Martingale (fun t : ℝ => M t.toNNReal) (realFiltration F) μ :=
  ⟨fun _ => hM.stronglyMeasurable _, fun _ _ h => hM.condExp_ae_eq (Real.toNNReal_mono h)⟩

lemma toNNReal_mem_Icc {T : ℝ≥0} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    t.toNNReal ∈ Set.Icc (0 : ℝ≥0) T := by
  constructor
  · exact bot_le
  · simpa only [Real.toNNReal_coe] using Real.toNNReal_mono ht.2

lemma toNNReal_point (T : ℝ≥0) (n i : ℕ) :
    (EnergyRiemann.point T n i).toNNReal = BrownianGrid.uniformGrid T n i := by
  apply NNReal.eq
  rw [Real.coe_toNNReal _ (by unfold EnergyRiemann.point; positivity)]
  simp only [EnergyRiemann.point, BrownianGrid.uniformGrid, NNReal.coe_div,
    NNReal.coe_mul, NNReal.coe_natCast]
  ring

theorem artanh_eq_stochasticLimit_add_primitive [IsProbabilityMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M A a : ℝ≥0 → Ω → ℝ} (T : ℝ≥0)
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (hMm : Measurable (fun p : ℝ≥0 × Ω => M p.1 p.2))
    (hcM : ∀ᵐ ω ∂μ, ContinuousOn (fun t => M t ω) (Set.Icc 0 T))
    (hcA : ∀ᵐ ω ∂μ, ContinuousOn (fun t => A t ω) (Set.Icc 0 T))
    (hmonoA : ∀ᵐ ω ∂μ, MonotoneOn (fun t => A t ω) (Set.Icc 0 T))
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hbound : ∀ᵐ ω ∂μ, ∀ t, |M t ω| ≤ r)
    {C : ℝ} (hC : 0 ≤ C) (htotal : ∀ᵐ ω ∂μ, A T ω - A 0 ω ≤ C)
    (ha : Integrable (fun p : ℝ × Ω => a p.1.toNNReal p.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) T)).prod μ))
    (hprimitive : ∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc 0 T,
      A t ω = A 0 ω + nnrealTimePrimitive a t ω)
    {L : Ω → ℝ} (hL : Integrable L μ)
    (hlinear : Tendsto (fun n => ∫ ω,
      |BrownianGrid.uniformSum M (fun t ω => ArtanhMartingaleFormula.firstWeight (M t ω))
        T (n + 1) ω - L ω| ∂μ) atTop (𝓝 0)) :
    (fun ω => Real.artanh (M T ω) - Real.artanh (M 0 ω)) =ᵐ[μ]
      fun ω => L ω + nnrealTimePrimitive
        (fun t ω => ArtanhMartingaleFormula.secondWeight (M t ω) * a t ω) T ω := by
  have hmeas : Measurable (fun p : ℝ × Ω => M p.1.toNNReal p.2) :=
    hMm.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hcM' : ∀ᵐ ω ∂μ, ContinuousOn (fun t : ℝ => M t.toNNReal ω)
      (Set.Icc (0 : ℝ) T) := by
    filter_upwards [hcM] with ω hω
    exact hω.comp continuous_real_toNNReal.continuousOn (fun _ ht => toNNReal_mem_Icc ht)
  have hcA' : ∀ᵐ ω ∂μ, ContinuousOn (fun t : ℝ => A t.toNNReal ω)
      (Set.Icc (0 : ℝ) T) := by
    filter_upwards [hcA] with ω hω
    exact hω.comp continuous_real_toNNReal.continuousOn (fun _ ht => toNNReal_mem_Icc ht)
  have hmonoA' : ∀ᵐ ω ∂μ, MonotoneOn (fun t : ℝ => A t.toNNReal ω)
      (Set.Icc (0 : ℝ) T) := by
    filter_upwards [hmonoA] with ω hω
    exact fun _ hs _ ht hst => hω (toNNReal_mem_Icc hs) (toNNReal_mem_Icc ht)
      (Real.toNNReal_mono hst)
  have hprim' : ∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      A t.toNNReal ω = A (0 : ℝ).toNNReal ω +
        ∫ s in (0 : ℝ)..t, a s.toNNReal ω := by
    filter_upwards [hprimitive] with ω hω
    intro t ht
    simpa only [Real.toNNReal_zero, nnrealTimePrimitive, Real.coe_toNNReal _ ht.1] using
      hω t.toNNReal (toNNReal_mem_Icc ht)
  have hlin' : Tendsto (fun n => ∫ ω,
      |ArtanhMartingaleFormula.linearSum (fun t : ℝ => M t.toNNReal)
        (EnergyRiemann.point T (n + 1)) (n + 1) ω - L ω| ∂μ) atTop (𝓝 0) := by
    simpa only [ArtanhMartingaleFormula.linearSum, BrownianGrid.uniformSum,
      BrownianGrid.integralSum, toNNReal_point] using hlinear
  have h := ArtanhMartingaleFormula.artanh_eq_stochasticLimit_add_integral T.coe_nonneg
    (martingale_realExtension hM) (martingale_realExtension hQ) hmeas hcM' hcA' hmonoA'
    hr0 hr (hbound.mono (fun ω hω t => hω t.toNNReal)) hC
    (by simpa only [Real.toNNReal_coe, Real.toNNReal_zero] using htotal)
    ha hprim' hL hlin'
  simpa only [Real.toNNReal_coe, Real.toNNReal_zero, nnrealTimePrimitive] using h

end Problem367.NNRealArtanhFormula

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ContinuousCoefficientModulus
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace Problem367.ContinuousCoefficientModulus

theorem pairModulus_nonneg (x y : ℕ → ℝ) (n : ℕ) :
    0 ≤ pairModulus x y n := NNReal.coe_nonneg _

theorem abs_sub_le_pairModulus (x y : ℕ → ℝ) {i n : ℕ} (hi : i < n) :
    |x i - y i| ≤ pairModulus x y n := by
  have h := Finset.le_sup (f := fun j => ‖x j - y j‖₊) (Finset.mem_range.mpr hi)
  exact_mod_cast h

theorem pairModulus_le (x y : ℕ → ℝ) (n : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i < n, |x i - y i| ≤ C) : pairModulus x y n ≤ C := by
  have h : (Finset.range n).sup (fun i => ‖x i - y i‖₊) ≤ (⟨C, hC⟩ : ℝ≥0) := by
    apply Finset.sup_le
    intro i hi
    exact_mod_cast hb i (Finset.mem_range.mp hi)
  exact_mod_cast h

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem stronglyMeasurable_pairModulus (x y : ℕ → Ω → ℝ)
    (hx : ∀ i, StronglyMeasurable (x i)) (hy : ∀ i, StronglyMeasurable (y i)) (n : ℕ) :
    StronglyMeasurable (fun ω => pairModulus (fun i => x i ω) (fun i => y i ω) n) := by
  induction n with
  | zero => simpa [pairModulus] using (stronglyMeasurable_const :
      StronglyMeasurable (fun _ : Ω => (0 : ℝ)))
  | succ n ih =>
    have h := ((((hx n).measurable.sub (hy n).measurable).norm).max
      ih.measurable).stronglyMeasurable
    simpa only [pairModulus, Finset.range_add_one, Finset.sup_insert,
      NNReal.coe_max, coe_nnnorm, Real.norm_eq_abs, Pi.sub_apply] using h

theorem memLp_pairModulus [IsFiniteMeasure μ] (x y : ℕ → Ω → ℝ)
    (hx : ∀ i, StronglyMeasurable (x i)) (hy : ∀ i, StronglyMeasurable (y i))
    (n : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i, i < n → ∀ᵐ ω ∂μ, |x i ω - y i ω| ≤ C) (p : ℝ≥0∞) :
    MemLp (fun ω => pairModulus (fun i => x i ω) (fun i => y i ω) n) p μ := by
  apply MemLp.of_bound (stronglyMeasurable_pairModulus x y hx hy n).aestronglyMeasurable C
  have hb' : ∀ i, ∀ᵐ ω ∂μ, i < n → |x i ω - y i ω| ≤ C := by
    intro i
    by_cases hi : i < n
    · exact (hb i hi).mono (fun _ h _ => h)
    · exact Filter.Eventually.of_forall (fun _ h => (hi h).elim)
  filter_upwards [ae_all_iff.2 hb'] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (pairModulus_nonneg _ _ _)]
  exact pairModulus_le _ _ _ hC hω

theorem tendsto_pairModulus_of_uniformContinuousOn
    {I : Type*} [PseudoMetricSpace I] {S : Set I} {H : I → ℝ}
    (hH : UniformContinuousOn H S) (s t : ℕ → ℕ → I) (N : ℕ → ℕ)
    (hs : ∀ n i, i < N n → s n i ∈ S) (ht : ∀ n i, i < N n → t n i ∈ S)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hdist : ∀ n i, i < N n → dist (s n i) (t n i) ≤ δ n) :
    Tendsto (fun n => pairModulus (fun i => H (s n i)) (fun i => H (t n i)) (N n))
      atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨η, hη, hlocal⟩ := Metric.uniformContinuousOn_iff.mp hH (ε / 2) (by positivity)
  obtain ⟨n₀, hn₀⟩ := (hδ.eventually (gt_mem_nhds hη)).exists_forall_of_atTop
  refine ⟨n₀, fun n hn => ?_⟩
  have hb : pairModulus (fun i => H (s n i)) (fun i => H (t n i)) (N n) ≤ ε / 2 := by
    apply pairModulus_le _ _ _ (by positivity)
    intro i hi
    have hh := hlocal (s n i) (hs n i hi) (t n i) (ht n i hi)
      ((hdist n i hi).trans_lt (hn₀ n hn))
    simpa only [Real.dist_eq] using hh.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (pairModulus_nonneg _ _ _)]
  linarith

theorem tendsto_integral_pairModulus_pow [IsFiniteMeasure μ]
    {I : Type*} [PseudoMetricSpace I] {S : Set I} (hS : IsCompact S)
    {H : I → Ω → ℝ} (hm : ∀ t, StronglyMeasurable (H t))
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => H t ω) S)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ t ∈ S, ∀ᵐ ω ∂μ, |H t ω| ≤ C)
    (s t : ℕ → ℕ → I) (N : ℕ → ℕ)
    (hs : ∀ n i, i < N n → s n i ∈ S) (ht : ∀ n i, i < N n → t n i ∈ S)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hdist : ∀ n i, i < N n → dist (s n i) (t n i) ≤ δ n)
    (p : ℕ) (hp : 0 < p) :
    Tendsto (fun n => ∫ ω,
      (pairModulus (fun i => H (s n i) ω) (fun i => H (t n i) ω) (N n)) ^ p ∂μ)
      atTop (𝓝 0) := by
  let R : ℕ → Ω → ℝ := fun n ω =>
    pairModulus (fun i => H (s n i) ω) (fun i => H (t n i) ω) (N n)
  have hRm (n : ℕ) : StronglyMeasurable (R n) :=
    stronglyMeasurable_pairModulus _ _ (fun i => hm (s n i)) (fun i => hm (t n i)) (N n)
  have hRb (n : ℕ) : ∀ᵐ ω ∂μ, |R n ω| ≤ 2 * C := by
    have hb' : ∀ i, ∀ᵐ ω ∂μ, i < N n → |H (s n i) ω - H (t n i) ω| ≤ 2 * C := by
      intro i
      by_cases hi : i < N n
      · filter_upwards [hb _ (hs n i hi), hb _ (ht n i hi)] with ω hsω htω
        intro _
        exact (abs_sub _ _).trans (by linarith)
      · exact Filter.Eventually.of_forall (fun _ h => (hi h).elim)
    filter_upwards [ae_all_iff.2 hb'] with ω hω
    rw [abs_of_nonneg (pairModulus_nonneg _ _ _)]
    exact pairModulus_le _ _ _ (by positivity) hω
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => R n ω) atTop (𝓝 0) := by
    filter_upwards [hc] with ω hω
    exact tendsto_pairModulus_of_uniformContinuousOn
      (hS.uniformContinuousOn_of_continuous hω) s t N hs ht δ hδ hdist
  have hh := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n ω => R n ω ^ p) (f := fun _ => (0 : ℝ))
    (fun _ => (2 * C) ^ p) (fun n => (hRm n).aestronglyMeasurable.pow p)
    (integrable_const _) ?_ ?_
  · simpa only [integral_zero] using hh
  · intro n
    filter_upwards [hRb n] with ω hω
    rw [norm_pow, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hω p
  · filter_upwards [hlim] with ω hω
    simpa only [zero_pow (Nat.ne_of_gt hp)] using hω.pow p

end Problem367.ContinuousCoefficientModulus

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_BracketIsometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators

namespace Problem367.MartingaleBracketIsometry

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem integrable_sq_mul {H D : Ω → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hH : AEStronglyMeasurable H μ) (hD : Integrable D μ)
    (hbound : ∀ᵐ ω ∂μ, |H ω| ≤ K) :
    Integrable (fun ω => H ω ^ 2 * D ω) μ := by
  apply hD.bdd_mul (c := K ^ 2) (hH.pow 2)
  filter_upwards [hbound] with ω hω
  simpa only [Real.norm_eq_abs, Pi.pow_apply, abs_sq, sq_abs] using
    (sq_le_sq₀ (abs_nonneg (H ω)) hK).2 hω

theorem integral_sq_mul_increment [IsFiniteMeasure μ]
    {I : Type*} [Preorder I] {F : Filtration I mΩ}
    {M A : I → Ω → ℝ} (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ) {s t : I} (hst : s ≤ t)
    {H : Ω → ℝ} (hH : StronglyMeasurable[F s] H)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ᵐ ω ∂μ, |H ω| ≤ K) :
    (∫ ω, (H ω * (M t ω - M s ω)) ^ 2 ∂μ) =
      ∫ ω, H ω ^ 2 * (A t ω - A s ω) ∂μ := by
  have hHae : AEStronglyMeasurable H μ := (hH.mono (F.le s)).aestronglyMeasurable
  have hD2 := (hM2 t).sub (hM2 s)
  have hHD2 : MemLp (fun ω => H ω * (M t ω - M s ω)) 2 μ :=
    MartingaleTransformL2.bounded_mul_memLp_two hHae hD2 hbound
  have hAint : Integrable (fun ω => A t ω - A s ω) μ :=
    (MartingaleQuadraticVariation.integrable_compensator hQ hM2 t).sub
      (MartingaleQuadraticVariation.integrable_compensator hQ hM2 s)
  have hHAint := integrable_sq_mul hK hHae hAint hbound
  have herr := MartingaleQuadraticVariation.integrable_squareError hQ hM2 s t
  have hHEint := integrable_sq_mul hK hHae herr hbound
  have hzero := SimpleIntegral.integral_mul_eq_zero_of_condExp_eq_zero
    (F.le s) (hH.pow 2) herr hHEint
    (MartingaleQuadraticVariation.condExp_squareError_eq_zero hM hQ hM2 hst)
  have hident : (fun ω => H ω ^ 2 *
      MartingaleQuadraticVariation.squareError M A s t ω) =
      (fun ω => (H ω * (M t ω - M s ω)) ^ 2) -
        (fun ω => H ω ^ 2 * (A t ω - A s ω)) := by
    funext ω
    simp only [MartingaleQuadraticVariation.squareError,
      MartingaleQuadraticVariation.increment, Pi.sub_apply]
    ring
  simp only [Pi.pow_apply] at hzero
  rw [hident] at hzero
  change (∫ ω, (H ω * (M t ω - M s ω)) ^ 2 -
    H ω ^ 2 * (A t ω - A s ω) ∂μ) = 0 at hzero
  rw [integral_sub hHD2.integrable_sq hHAint] at hzero
  exact sub_eq_zero.mp hzero

theorem integral_sq_transform [IsFiniteMeasure μ]
    {F : Filtration ℕ mΩ} {M A H : ℕ → Ω → ℝ}
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ) (hH : StronglyAdapted F H)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ i, ∀ᵐ ω ∂μ, |H i ω| ≤ K)
    (s : Finset ℕ) :
    (∫ ω, (∑ i ∈ s, H i ω * (M (i + 1) ω - M i ω)) ^ 2 ∂μ) =
      ∑ i ∈ s, ∫ ω, H i ω ^ 2 * (A (i + 1) ω - A i ω) ∂μ := by
  rw [MartingaleTransformL2.integral_sq_transform hM hM2 hH hbound]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_sq_mul_increment hM hQ hM2 (Nat.le_succ i) (hH i) hK (hbound i)

theorem integral_sq_transform_le_random_envelope [IsFiniteMeasure μ]
    {F : Filtration ℕ mΩ} {M A H : ℕ → Ω → ℝ}
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ) (hH : StronglyAdapted F H)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ i, ∀ᵐ ω ∂μ, |H i ω| ≤ K)
    (s : Finset ℕ) {R : Ω → ℝ} (hR : Integrable R μ)
    (hRnonneg : ∀ᵐ ω ∂μ, 0 ≤ R ω)
    (hEnvelope : ∀ᵐ ω ∂μ, ∀ i ∈ s, H i ω ^ 2 ≤ R ω)
    (hA : ∀ᵐ ω ∂μ, ∀ i ∈ s, 0 ≤ A (i + 1) ω - A i ω)
    {C : ℝ} (htotal : ∀ᵐ ω ∂μ, (∑ i ∈ s, (A (i + 1) ω - A i ω)) ≤ C) :
    (∫ ω, (∑ i ∈ s, H i ω * (M (i + 1) ω - M i ω)) ^ 2 ∂μ) ≤
      C * ∫ ω, R ω ∂μ := by
  have hint (i : ℕ) : Integrable (fun ω => H i ω ^ 2 *
      (A (i + 1) ω - A i ω)) μ :=
    integrable_sq_mul hK ((hH i).mono (F.le i)).aestronglyMeasurable
      ((MartingaleQuadraticVariation.integrable_compensator hQ hM2 (i + 1)).sub
        (MartingaleQuadraticVariation.integrable_compensator hQ hM2 i)) (hbound i)
  rw [integral_sq_transform hM hQ hM2 hH hK hbound,
    ← integral_finsetSum s (fun i _ => hint i), ← integral_const_mul]
  apply integral_mono_ae (integrable_finsetSum s (fun i _ => hint i)) (hR.const_mul C)
  filter_upwards [hRnonneg, hEnvelope, hA, htotal] with ω hRω hEω hAω htω
  calc
    (∑ i ∈ s, H i ω ^ 2 * (A (i + 1) ω - A i ω)) ≤
        ∑ i ∈ s, R ω * (A (i + 1) ω - A i ω) := by
      exact Finset.sum_le_sum (fun i hi =>
        mul_le_mul_of_nonneg_right (hEω i hi) (hAω i hi))
    _ = R ω * (∑ i ∈ s, (A (i + 1) ω - A i ω)) := by rw [Finset.mul_sum]
    _ ≤ R ω * C := mul_le_mul_of_nonneg_left htω hRω
    _ = C * R ω := mul_comm _ _

theorem integral_sq_grid_transform_le_random_envelope [IsFiniteMeasure μ]
    {I : Type*} [Preorder I] {F : Filtration I mΩ} {M A : I → Ω → ℝ}
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ)
    (t : ℕ → I) (ht : Monotone t) (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[F (t i)] (H i))
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ i, ∀ᵐ ω ∂μ, |H i ω| ≤ K)
    (n : ℕ) {R : Ω → ℝ} (hR : Integrable R μ)
    (hRnonneg : ∀ᵐ ω ∂μ, 0 ≤ R ω)
    (hEnvelope : ∀ᵐ ω ∂μ, ∀ i < n, H i ω ^ 2 ≤ R ω)
    (hA : ∀ᵐ ω ∂μ, Monotone (fun u => A u ω))
    {C : ℝ} (htotal : ∀ᵐ ω ∂μ, A (t n) ω - A (t 0) ω ≤ C) :
    (∫ ω, (∑ i ∈ Finset.range n,
      H i ω * (M (t (i + 1)) ω - M (t i) ω)) ^ 2 ∂μ) ≤
      C * ∫ ω, R ω ∂μ := by
  let G : Filtration ℕ mΩ :=
    ⟨fun i => F (t i), fun _ _ hij => F.mono (ht hij), fun i => F.le (t i)⟩
  have hMG : Martingale (fun i => M (t i)) G μ :=
    ⟨fun i => hM.stronglyMeasurable (t i), fun _ _ hij => hM.condExp_ae_eq (ht hij)⟩
  have hQG : Martingale (fun i ω => M (t i) ω ^ 2 - A (t i) ω) G μ :=
    ⟨fun i => hQ.stronglyMeasurable (t i), fun _ _ hij => hQ.condExp_ae_eq (ht hij)⟩
  apply integral_sq_transform_le_random_envelope hMG hQG
    (fun i => hM2 (t i)) hH hK hbound (Finset.range n) hR hRnonneg
  · filter_upwards [hEnvelope] with ω hω
    exact fun i hi => hω i (Finset.mem_range.mp hi)
  · filter_upwards [hA] with ω hω
    exact fun i _ => sub_nonneg.mpr (hω (ht (Nat.le_succ i)))
  · filter_upwards [htotal] with ω hω
    have htel : (∑ i ∈ Finset.range n, (A (t (i + 1)) ω - A (t i) ω)) =
        A (t n) ω - A (t 0) ω := by
      clear hEnvelope htotal hω
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        ring
    simpa only [htel] using hω

theorem tendsto_integral_sq_grid_transform [IsFiniteMeasure μ]
    {I : Type*} [Preorder I] {F : Filtration I mΩ} {M A : I → Ω → ℝ}
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ)
    (t : ℕ → ℕ → I) (ht : ∀ k, Monotone (t k))
    (H : ℕ → ℕ → Ω → ℝ) (hH : ∀ k i, StronglyMeasurable[F (t k i)] (H k i))
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ k i, ∀ᵐ ω ∂μ, |H k i ω| ≤ K)
    (N : ℕ → ℕ) {R : ℕ → Ω → ℝ} (hR : ∀ k, Integrable (R k) μ)
    (hRnonneg : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ R k ω)
    (hEnvelope : ∀ k, ∀ᵐ ω ∂μ, ∀ i < N k, H k i ω ^ 2 ≤ R k ω)
    (hA : ∀ᵐ ω ∂μ, Monotone (fun u => A u ω))
    {C : ℝ} (htotal : ∀ k, ∀ᵐ ω ∂μ, A (t k (N k)) ω - A (t k 0) ω ≤ C)
    (hlim : Tendsto (fun k => ∫ ω, R k ω ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, (∑ i ∈ Finset.range (N k),
      H k i ω * (M (t k (i + 1)) ω - M (t k i) ω)) ^ 2 ∂μ) atTop (𝓝 0) := by
  apply squeeze_zero (fun k => integral_nonneg (fun ω => sq_nonneg _))
    (fun k => ?_) (by simpa using hlim.const_mul C)
  exact integral_sq_grid_transform_le_random_envelope hM hQ hM2 (t k) (ht k)
    (H k) (hH k) hK (hbound k) (N k) (hR k) (hRnonneg k)
    (hEnvelope k) hA (htotal k)

end Problem367.MartingaleBracketIsometry

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_UniformIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.MartingaleUniformIntegral

open BrownianGrid ContinuousCoefficientModulus

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem uniformSum_memLp {F : Filtration ℝ≥0 mΩ} {M H : ℝ≥0 → Ω → ℝ}
    (hM2 : ∀ t, MemLp (M t) 2 μ) (hH : StronglyAdapted F H)
    {K : ℝ} (hb : ∀ t, ∀ᵐ ω ∂μ, |H t ω| ≤ K) (T : ℝ≥0) (n : ℕ) :
    MemLp (uniformSum M H T n) 2 μ := by
  unfold uniformSum integralSum
  apply memLp_finsetSum
  intro i hi
  exact MartingaleTransformL2.bounded_mul_memLp_two
    ((hH _).mono (F.le _)).aestronglyMeasurable
    ((hM2 _).sub (hM2 _)) (hb _)

theorem tendsto_integral_sq_refinement [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M A H : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ) (hH : StronglyAdapted F H)
    (T : ℝ≥0) (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => H t ω) (Icc 0 T))
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t, ∀ᵐ ω ∂μ, |H t ω| ≤ K)
    (hA : ∀ᵐ ω ∂μ, Monotone (fun t => A t ω))
    {C : ℝ} (htotal : ∀ᵐ ω ∂μ, A T ω - A 0 ω ≤ C)
    (n k : ℕ → ℕ) (hn : ∀ j, 0 < n j) (hk : ∀ j, 0 < k j)
    (hnlim : Tendsto n atTop atTop) :
    Tendsto (fun j => ∫ ω,
      (uniformSum M H T (n j) ω - uniformSum M H T (n j * k j) ω) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  let s : ℕ → ℕ → ℝ≥0 := fun j i => uniformGrid T (n j) (i / k j)
  let t : ℕ → ℕ → ℝ≥0 := fun j i => uniformGrid T (n j * k j) i
  let N : ℕ → ℕ := fun j => n j * k j
  let D : ℕ → ℕ → Ω → ℝ := fun j i ω => H (s j i) ω - H (t j i) ω
  let R : ℕ → Ω → ℝ := fun j ω =>
    pairModulus (fun i => H (s j i) ω) (fun i => H (t j i) ω) (N j)
  have hHm (u : ℝ≥0) : StronglyMeasurable (H u) := (hH u).mono (F.le u)
  have hle (j i : ℕ) : s j i ≤ t j i := uniformGrid_floor_le T (hn j) (hk j) i
  have htmem (j i : ℕ) (hi : i < N j) : t j i ∈ Icc 0 T :=
    ⟨zero_le, uniformGrid_le_horizon T (Nat.mul_pos (hn j) (hk j)) hi.le⟩
  have hsmem (j i : ℕ) (hi : i < N j) : s j i ∈ Icc 0 T :=
    ⟨zero_le, (hle j i).trans (htmem j i hi).2⟩
  have hDb (j i : ℕ) : ∀ᵐ ω ∂μ, |D j i ω| ≤ 2 * K := by
    filter_upwards [hb (s j i), hb (t j i)] with ω hsω htω
    exact (abs_sub _ _).trans (by linarith)
  have hR2 (j : ℕ) : MemLp (R j) 2 μ :=
    memLp_pairModulus _ _ (fun i => hHm (s j i)) (fun i => hHm (t j i)) (N j)
      (show 0 ≤ 2 * K by positivity) (fun i _ => hDb j i) 2
  have hδ : Tendsto (fun j => (T : ℝ) / (n j : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hnlim)
  have hd (j i : ℕ) (_hi : i < N j) :
      dist (s j i) (t j i) ≤ (T : ℝ) / (n j : ℝ) := by
    change |(s j i : ℝ) - (t j i : ℝ)| ≤ _
    rw [abs_of_nonpos (sub_nonpos.mpr (NNReal.coe_le_coe.mpr (hle j i)))]
    have hh := uniformGrid_floor_sub_le T (hn j) (hk j) i
    change (t j i : ℝ) - (s j i : ℝ) ≤ _ at hh
    linarith
  have hRlim : Tendsto (fun j => ∫ ω, R j ω ^ 2 ∂μ) atTop (𝓝 0) :=
    tendsto_integral_pairModulus_pow isCompact_Icc hHm hc hK (fun u _ => hb u)
      s t N hsmem htmem _ hδ hd 2 (by decide)
  have hlim := MartingaleBracketIsometry.tendsto_integral_sq_grid_transform hM hQ hM2
    t (fun j => uniformGrid_mono T (N j)) D
    (fun j i => ((hH (s j i)).mono (F.mono (hle j i))).sub (hH (t j i)))
    (show 0 ≤ 2 * K by positivity) hDb N
    (R := fun j ω => R j ω ^ 2) (fun j => (hR2 j).integrable_sq)
    (fun _ => Filter.Eventually.of_forall (fun ω => sq_nonneg _))
    (fun j => Filter.Eventually.of_forall (fun ω i hi => by
      have hh := abs_sub_le_pairModulus (fun i => H (s j i) ω) (fun i => H (t j i) ω) hi
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) (pairModulus_nonneg _ _ _)).2 hh)) hA
    (C := C) (fun j => by
      simpa only [t, N, uniformGrid_end T (Nat.mul_pos (hn j) (hk j)), uniformGrid_zero] using htotal)
    hRlim
  have href (j : ℕ) : uniformSum M H T (n j) =
      integralSum M (t j) (fun i => H (s j i)) (N j) := by
    have hh := integralSum_refinement M (t j)
      (fun i => H (uniformGrid T (n j) i)) (n j) (hk j)
    simpa only [t, s, N, uniformGrid_refine T (hn j) (hk j), uniformSum] using hh
  apply hlim.congr'
  apply Filter.Eventually.of_forall
  intro j
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  rw [href j]
  simp only [uniformSum, integralSum, D, t, N, sub_mul, Finset.sum_sub_distrib]

theorem exists_uniform_integral [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M A H : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ) (hH : StronglyAdapted F H)
    (T : ℝ≥0) (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => H t ω) (Icc 0 T))
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t, ∀ᵐ ω ∂μ, |H t ω| ≤ K)
    (hA : ∀ᵐ ω ∂μ, Monotone (fun t => A t ω))
    {C : ℝ} (htotal : ∀ᵐ ω ∂μ, A T ω - A 0 ω ≤ C) :
    ∃ L : Ω → ℝ, StronglyMeasurable L ∧ MemLp L 2 μ ∧
      Tendsto (fun n => ∫ ω, (uniformSum M H T n ω - L ω) ^ 2 ∂μ) atTop (𝓝 0) := by
  have hS (n : ℕ) : MemLp (uniformSum M H T n) 2 μ := uniformSum_memLp hM2 hH hb T n
  let f : ℕ → Lp ℝ 2 μ := fun n => (hS n).toLp (uniformSum M H T n)
  have hf : CauchySeq f := by
    by_contra hnot
    rw [Metric.cauchySeq_iff] at hnot
    push Not at hnot
    obtain ⟨ε, hε, hbad⟩ := hnot
    choose n hn m hm hsep using hbad
    let u : ℕ → ℕ := fun j => n (j + 1)
    let v : ℕ → ℕ := fun j => m (j + 1)
    have hu (j : ℕ) : 0 < u j := (Nat.succ_pos j).trans_le (hn (j + 1))
    have hv (j : ℕ) : 0 < v j := (Nat.succ_pos j).trans_le (hm (j + 1))
    have hulim : Tendsto u atTop atTop := by
      apply tendsto_atTop.2
      intro b
      filter_upwards [eventually_ge_atTop b] with j hj
      exact hj.trans ((Nat.le_succ j).trans (hn (j + 1)))
    have hvlim : Tendsto v atTop atTop := by
      apply tendsto_atTop.2
      intro b
      filter_upwards [eventually_ge_atTop b] with j hj
      exact hj.trans ((Nat.le_succ j).trans (hm (j + 1)))
    have hleft := tendsto_integral_sq_refinement hM hQ hM2 hH T hc hK hb hA htotal
      u v hu hv hulim
    have hright := tendsto_integral_sq_refinement hM hQ hM2 hH T hc hK hb hA htotal
      v u hv hu hvlim
    have hright' : Tendsto (fun j => ∫ ω,
        (uniformSum M H T (v j) ω - uniformSum M H T (u j * v j) ω) ^ 2 ∂μ)
        atTop (𝓝 0) := by simpa only [Nat.mul_comm] using hright
    have hbound (j : ℕ) : ε ^ 2 ≤
        2 * (∫ ω, (uniformSum M H T (u j) ω - uniformSum M H T (u j * v j) ω) ^ 2 ∂μ) +
        2 * (∫ ω, (uniformSum M H T (v j) ω - uniformSum M H T (u j * v j) ω) ^ 2 ∂μ) := by
      have hs : ε ≤ ‖f (u j) - f (v j)‖ := by
        simpa only [dist_eq_norm] using hsep (j + 1)
      have hsq := (sq_le_sq₀ hε.le (norm_nonneg _)).2 hs
      have hnorm : ‖f (u j) - f (v j)‖ ^ 2 =
          ∫ ω, (uniformSum M H T (u j) ω - uniformSum M H T (v j) ω) ^ 2 ∂μ :=
        BrownianGrid.norm_sq_toLp_sub (hS _) (hS _)
      rw [hnorm] at hsq
      exact hsq.trans (integral_sq_sub_le_two (hS _) (hS _) (hS _))
    have hzero := (hleft.const_mul 2).add (hright'.const_mul 2)
    have hcontra := ge_of_tendsto hzero (Filter.Eventually.of_forall hbound)
    nlinarith [sq_pos_of_pos hε]
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hf
  refine ⟨L, Lp.stronglyMeasurable L, Lp.memLp L, ?_⟩
  have hnorm := (hL.sub (tendsto_const_nhds (x := L))).norm.pow 2
  simp only [sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hnorm
  apply hnorm.congr'
  apply Filter.Eventually.of_forall
  intro n
  have hh := BrownianGrid.norm_sq_toLp_sub (hS n) (Lp.memLp L)
  simpa only [Lp.toLp_coeFn, f] using hh

theorem exists_uniform_integral_on [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M A H : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ) (hH : StronglyAdapted F H)
    (T : ℝ≥0) (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => H t ω) (Icc 0 T))
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t ∈ Icc 0 T, ∀ᵐ ω ∂μ, |H t ω| ≤ K)
    (hA : ∀ᵐ ω ∂μ, MonotoneOn (fun t => A t ω) (Icc 0 T))
    {C : ℝ} (htotal : ∀ᵐ ω ∂μ, A T ω - A 0 ω ≤ C) :
    ∃ L : Ω → ℝ, StronglyMeasurable L ∧ MemLp L 2 μ ∧
      Tendsto (fun n => ∫ ω, (uniformSum M H T n ω - L ω) ^ 2 ∂μ) atTop (𝓝 0) := by
  let q : ℝ≥0 → ℝ≥0 := fun u => min u T
  have hqm : Monotone q := monotone_id.min monotone_const
  have hqmem (u : ℝ≥0) : q u ∈ Icc 0 T := ⟨zero_le, min_le_right _ _⟩
  let G : Filtration ℝ≥0 mΩ :=
    ⟨fun u => F (q u), fun _ _ h => F.mono (hqm h), fun u => F.le (q u)⟩
  have hMG : Martingale (fun u => M (q u)) G μ :=
    ⟨fun u => hM.stronglyMeasurable _, fun _ _ h => hM.condExp_ae_eq (hqm h)⟩
  have hQG : Martingale (fun u ω => M (q u) ω ^ 2 - A (q u) ω) G μ :=
    ⟨fun u => hQ.stronglyMeasurable _, fun _ _ h => hQ.condExp_ae_eq (hqm h)⟩
  have hHc : ∀ᵐ ω ∂μ, ContinuousOn (fun u => H (q u) ω) (Icc 0 T) := by
    filter_upwards [hc] with ω hω
    apply hω.congr
    intro u hu
    simp only [q, min_eq_left hu.2]
  have hAm : ∀ᵐ ω ∂μ, Monotone (fun u => A (q u) ω) := by
    filter_upwards [hA] with ω hω
    exact fun u v huv => hω (hqmem u) (hqmem v) (hqm huv)
  obtain ⟨L, hLm, hL2, hlim⟩ := exists_uniform_integral hMG hQG
    (fun u => hM2 (q u)) (fun u => hH (q u)) T hHc hK
    (fun u => hb (q u) (hqmem u)) hAm
    (C := C) (by simpa only [q, min_self, min_eq_left (show (0 : ℝ≥0) ≤ T from zero_le)] using htotal)
  have hsum (n : ℕ) : uniformSum (fun u => M (q u)) (fun u => H (q u)) T n =
      uniformSum M H T n := by
    funext ω
    unfold uniformSum integralSum
    apply Finset.sum_congr rfl
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have hn : 0 < n := (Nat.zero_le i).trans_lt hin
    have hleft := uniformGrid_le_horizon T hn hin.le
    have hright := uniformGrid_le_horizon T hn (Nat.succ_le_of_lt hin)
    simp only [q, min_eq_left hleft, min_eq_left hright]
  exact ⟨L, hLm, hL2, by simpa only [hsum] using hlim⟩

end Problem367.MartingaleUniformIntegral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ConstructedArtanhFormula
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.innovationPath_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.ConstructedArtanhFormula

open ArtanhMartingaleFormula

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem exists_artanh_decomposition_oai [IsProbabilityMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M A a : ℝ≥0 → Ω → ℝ} (T : ℝ≥0)
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (hMm : Measurable (fun p : ℝ≥0 × Ω => M p.1 p.2))
    (hcM : ∀ᵐ ω ∂μ, ContinuousOn (fun t => M t ω) (Icc 0 T))
    (hcA : ∀ᵐ ω ∂μ, ContinuousOn (fun t => A t ω) (Icc 0 T))
    (hmonoA : ∀ᵐ ω ∂μ, MonotoneOn (fun t => A t ω) (Icc 0 T))
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hbound : ∀ᵐ ω ∂μ, ∀ t, |M t ω| ≤ r)
    {C : ℝ} (hC : 0 ≤ C) (htotal : ∀ᵐ ω ∂μ, A T ω - A 0 ω ≤ C)
    (ha : Integrable (fun p : ℝ × Ω => a p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod μ))
    (hprimitive : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      A t ω = A 0 ω + nnrealTimePrimitive a t ω) :
    ∃ L : Ω → ℝ, StronglyMeasurable L ∧ MemLp L 2 μ ∧
      Tendsto (fun n => ∫ ω,
        (BrownianGrid.uniformSum M (fun t ω => firstWeight (M t ω)) T n ω - L ω) ^ 2 ∂μ)
        atTop (𝓝 0) ∧
      (fun ω => Real.artanh (M T ω) - Real.artanh (M 0 ω)) =ᵐ[μ]
        fun ω => L ω + nnrealTimePrimitive
          (fun t ω => secondWeight (M t ω) * a t ω) T ω := by
  let H : ℝ≥0 → Ω → ℝ := fun t ω => firstWeight (M t ω)
  have hd : 0 < 1 - r ^ 2 := by nlinarith
  have hM2 (t : ℝ≥0) : MemLp (M t) 2 μ := by
    apply MemLp.of_bound ((hM.stronglyMeasurable t).mono (F.le t)).aestronglyMeasurable r
    filter_upwards [hbound] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  have hH : StronglyAdapted F H := fun t => stronglyMeasurable_firstWeight (hM.stronglyMeasurable t)
  have hHb (t : ℝ≥0) : ∀ᵐ ω ∂μ, |H t ω| ≤ 1 / (1 - r ^ 2) :=
    hbound.mono (fun ω hω => firstWeight_bound hr0 hr (hω t))
  have hHc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => H t ω) (Icc 0 T) := by
    filter_upwards [hcM, hbound] with ω hc hb
    apply continuousOn_const.div (continuousOn_const.sub (hc.pow 2))
    intro t ht
    have hs : M t ω ^ 2 ≤ r ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hr0).2 (hb t)
    change 1 - M t ω ^ 2 ≠ 0
    linarith
  obtain ⟨L, hLm, hL2, hlim⟩ := MartingaleUniformIntegral.exists_uniform_integral_on
    hM hQ hM2 hH T hHc (show 0 ≤ 1 / (1 - r ^ 2) by positivity)
    (fun t _ => hHb t) hmonoA htotal
  have hL1 := tendsto_integral_abs_zero_of_sq
    (fun n ω => BrownianGrid.uniformSum M H T n ω - L ω)
    (fun n => (MartingaleUniformIntegral.uniformSum_memLp hM2 hH hHb T n).sub hL2) hlim
  refine ⟨L, hLm, hL2, hlim, ?_⟩
  apply NNRealArtanhFormula.artanh_eq_stochasticLimit_add_primitive T hM hQ hMm
    hcM hcA hmonoA hr0 hr hbound hC htotal ha hprimitive
    (hL2.integrable (by norm_num))
  simpa only [Function.comp_def, H] using hL1.comp (tendsto_add_atTop_nat 1)

end Problem367.ConstructedArtanhFormula

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Problem367.ConstructedArtanhFormula.exists_artanh_decomposition_oai.{u_1} := @OAI.Problem367.ConstructedArtanhFormula.exists_artanh_decomposition_oai.{u_1}
