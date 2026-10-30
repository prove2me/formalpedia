-- Prove2me | solution 1 for OAI.Falconer.exists_policy_prefix_common_budgets
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:18:40.132805+00:00
-- url     : https://prove2.me/submissions/3a0c7aa9-1927-4974-9936-f9baaa2c33ac

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002
import Theorems.Thm_OAI_Falconer_dyadic_profile_graph_energy_step
import Theorems.Thm_OAI_Falconer_exists_policy_scalar_conversion

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_RadialShellMass
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem sourceAngularShellMeasure_mass_le (v : ℝ) (Ψ : ℝ → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ t, Ψ t ≤ B)
    (hs : ∀ t, 4 < t → Ψ t = 0) :
    sourceAngularShellMeasure v Ψ univ ≤ ENNReal.ofReal (4*B) := by
  let A : ℝ := (2:ℝ)^v
  have hA : 0 < A := Real.rpow_pos_of_pos (by norm_num) _
  unfold sourceAngularShellMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  change (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (Ψ (r/A)/A)) ≤ _
  calc
    _ ≤ ∫⁻ r in Ioi (0:ℝ), (Iic (4*A)).indicator (fun _ => ENNReal.ofReal (B/A)) r := by
      apply lintegral_mono
      intro r
      dsimp only
      by_cases hr : r ≤ 4*A
      · rw [indicator_of_mem (show r ∈ Iic (4*A) from hr)]
        exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hb _) hA.le)
      · rw [indicator_of_notMem (show r ∉ Iic (4*A) from hr)]
        rw [hs _ ((lt_div_iff₀ hA).mpr (lt_of_not_ge hr)), zero_div, ENNReal.ofReal_zero]
    _ = ENNReal.ofReal (B/A) * ENNReal.ofReal (4*A) := by
      rw [lintegral_indicator measurableSet_Iic, lintegral_const, Measure.restrict_apply_univ,
        Measure.restrict_apply measurableSet_Iic]
      rw [inter_comm, Ioi_inter_Iic, Real.volume_Ioc, sub_zero]
    _ = ENNReal.ofReal (4*B) := by
      rw [← ENNReal.ofReal_mul (div_nonneg hB hA.le)]
      congr 1
      rw [mul_left_comm, div_mul_cancel₀ _ hA.ne']

theorem sourceAngularShellMeasure_finite (v : ℝ) (Ψ : ℝ → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ t, Ψ t ≤ B)
    (hs : ∀ t, 4 < t → Ψ t = 0) : IsFiniteMeasure (sourceAngularShellMeasure v Ψ) :=
  ⟨(sourceAngularShellMeasure_mass_le v Ψ hB hb hs).trans_lt ENNReal.ofReal_lt_top⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SphericalEnergy
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Independent angular energy in every dimension

The angular measure is the actual sphere measure obtained from Euclidean
Lebesgue measure by polar coordinates. The radial measure is the same
nonnegative shell cutoff used by the scalar reconstruction. Both angular
variables remain independent in this energy.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem sphereMoment_nonneg {d : ℕ} (U : ℝ × Sphere d → ℂ) (r : ℝ) :
    0 ≤ sphereMoment U r := integral_nonneg (fun _ => sq_nonneg _)

theorem sphereMoment_measurable {d : ℕ} (U : ℝ × Sphere d → ℂ)
    (hU : Measurable U) : Measurable (sphereMoment U) :=
  (hU.norm.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable

theorem sphere_norm_square_integrable {d : ℕ} (U : Sphere d → ℂ) (hU : Measurable U)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ w, ‖U w‖ ≤ C) :
    Integrable (fun w => ‖U w‖^2) (sphereMeasure d) := by
  apply Integrable.of_bound (hU.norm.pow_const 2).aestronglyMeasurable (C^2)
  filter_upwards with w
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg _) hC).mpr (hb w)

theorem sphereMoment_le {d : ℕ} (U : ℝ × Sphere d → ℂ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ z, ‖U z‖ ≤ C) (r : ℝ) :
    sphereMoment U r ≤ C^2 * (sphereMeasure d).real univ := by
  apply (le_abs_self _).trans
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le_const
  filter_upwards with w
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg _) hC).mpr (hb (r,w))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SharedAngular
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Shared-angle energy and the independent-angle bound

The shell conversion uses one shared angular variable. Cauchy--Schwarz
transfers it to the positive independent-angle energy with exactly the
same endpoint symbols and radial measure.
-/

namespace Falconer
open Set MeasureTheory

theorem independentAngularIntegrand_integrable {d : ℕ} (v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (U V : ℝ × Sphere d → ℂ) (hU : Measurable U) (hV : Measurable V)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbU : ∀ z, ‖U z‖ ≤ C) (hbV : ∀ z, ‖V z‖ ≤ D) :
    Integrable (fun r => sphereMoment U r * sphereMoment V r)
      (PlanarFalconer.sourceAngularShellMeasure v Ψ) := by
  apply Integrable.of_bound
    ((sphereMoment_measurable U hU).mul (sphereMoment_measurable V hV)).aestronglyMeasurable
    ((C^2 * (sphereMeasure d).real univ) * (D^2 * (sphereMeasure d).real univ))
  filter_upwards with r
  change ‖sphereMoment U r * sphereMoment V r‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (sphereMoment_nonneg U r) (sphereMoment_nonneg V r))]
  exact mul_le_mul (sphereMoment_le U hC hbU r) (sphereMoment_le V hD hbV r)
    (sphereMoment_nonneg V r) (by positivity)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_EndpointTransform
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Original endpoint transforms in arbitrary dimension

The spatial measure argument is already restricted to its cell. A child
therefore uses the same endpoint symbol and the original restricted law.
The exact finite-measure splitting keeps the model-mass factors explicit.
-/

namespace Falconer
open MeasureTheory

theorem endpoint_integrand_norm {d : ℕ} (b : Space d → Sphere d → ℂ)
    (r : ℝ) (w : Sphere d) (x : Space d) :
    ‖Complex.exp (Complex.I * (r : ℂ) * (inner ℝ (w : Space d) x : ℂ)) * b x w‖ = ‖b x w‖ := by
  simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem measurable_endpointTransform {d : ℕ} (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (M : ℝ) (b : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) :
    Measurable (fun z : ℝ × Sphere d => endpointTransform ρ M b z.1 z.2) := by
  have hf : Measurable (fun z : (ℝ × Sphere d) × Space d =>
      Complex.exp (Complex.I * (z.1.1 : ℂ) * (inner ℝ (z.1.2 : Space d) z.2 : ℂ)) *
        b z.2 z.1.2) := by
    apply Measurable.mul
    · fun_prop
    · exact hb.comp (measurable_snd.prodMk measurable_fst.snd)
  have hi := (hf.stronglyMeasurable.integral_prod_right' (ν := ρ)).measurable
  exact (measurable_const (a := (M⁻¹ : ℝ))).smul hi

theorem endpointTransform_norm_le {d : ℕ} (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    {M C : ℝ} (hM : 0 < M) (b : Space d → Sphere d → ℂ)
    (hC : ∀ x w, ‖b x w‖ ≤ C) (r : ℝ) (w : Sphere d) :
    ‖endpointTransform ρ M b r w‖ ≤ C * ρ.real Set.univ / M := by
  unfold endpointTransform
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hM)]
  have hb := norm_integral_le_of_norm_le_const (μ := ρ)
    (Filter.Eventually.of_forall (fun x => (endpoint_integrand_norm b r w x).trans_le (hC x w)))
  calc
    _ ≤ M⁻¹ * (C * ρ.real Set.univ) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hM.le)
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularTerminal
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Terminal independent angular energies in every dimension

Only the sup norm of the actual endpoint symbols and the two original
cell masses enter the stopping estimate. The radial shell measure is
normalized, so its total mass has no frequency factor.
-/

namespace Falconer
open MeasureTheory Set

theorem independentAngularEnergy_bound {d : ℕ} (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (U V : ℝ × Sphere d → ℂ) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbU : ∀ z, ‖U z‖ ≤ C) (hbV : ∀ z, ‖V z‖ ≤ D) :
    independentAngularEnergy a v Ψ U V ≤
      (2:ℝ)^((d:ℝ)*(v-a)) * (C^2*D^2*(sphereMeasure d).real univ^2) *
        (PlanarFalconer.sourceAngularShellMeasure v Ψ).real univ := by
  have hb : ∀ r, ‖sphereMoment U r*sphereMoment V r‖ ≤
      C^2*D^2*(sphereMeasure d).real univ^2 := by
    intro r
    rw [Real.norm_eq_abs,abs_of_nonneg
      (mul_nonneg (sphereMoment_nonneg U r) (sphereMoment_nonneg V r))]
    calc
      _ ≤ (C^2*(sphereMeasure d).real univ)*(D^2*(sphereMeasure d).real univ) :=
        mul_le_mul (sphereMoment_le U hC hbU r) (sphereMoment_le V hD hbV r)
          (sphereMoment_nonneg V r) (by positivity)
      _ = _ := by ring
  unfold independentAngularEnergy
  have hnorm := norm_integral_le_of_norm_le_const
    (μ := PlanarFalconer.sourceAngularShellMeasure v Ψ) (Filter.Eventually.of_forall hb)
  have hn : 0 ≤ ∫ r, sphereMoment U r*sphereMoment V r
      ∂PlanarFalconer.sourceAngularShellMeasure v Ψ :=
    integral_nonneg (fun r => mul_nonneg (sphereMoment_nonneg U r) (sphereMoment_nonneg V r))
  rw [Real.norm_eq_abs,abs_of_nonneg hn] at hnorm
  exact (mul_le_mul_of_nonneg_left hnorm (by positivity)).trans_eq (by ring)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_SmoothReciprocal
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth reciprocal of a nonstationary phase derivative

The reciprocal is extended smoothly across zero by a scalar bump. At a
point where the denominator is bounded below, its derivative bounds
depend only on the normalized derivatives of that denominator.
-/

namespace Falconer
open Set Metric
open scoped ContDiff Topology

theorem smoothReciprocal_eq {τ u : ℝ} (hτ : 0 < τ) (hu : τ ≤ |u|) :
    u * smoothReciprocal τ hτ u = 1 := by
  have hb : PlanarFalconer.sineZeroCutoff τ hτ u = 0 :=
    (PlanarFalconer.sineZeroCutoff τ hτ).zero_of_le_dist
      (by simpa [PlanarFalconer.sineZeroCutoff, Real.dist_eq] using hu)
  have hune : u ≠ 0 := by intro he; simp [he] at hu; linarith
  simp [smoothReciprocal,hb,hune]

/-- The derivative constants are independent of the denominator, its
lower bound, and the frequency scale. Only positive-order derivatives
of the denominator enter the recurrence. -/
theorem reciprocal_germ_derivatives (B : ℕ → ℝ) (hB : ∀ k, 0 ≤ B k) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g q : ℝ → ℝ), ContDiff ℝ ∞ g → ContDiff ℝ ∞ q →
      ∀ (τ D x : ℝ), 0 < τ → 0 ≤ D → τ ≤ |g x| →
      (fun y => q y * g y) =ᶠ[𝓝 x] (fun _ => 1) →
      (∀ k, 1 ≤ k → k ≤ n → |iteratedDeriv k g x| ≤ B k * τ * D^k) →
      |iteratedDeriv n q x| ≤ C * τ⁻¹ * D^n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      refine ⟨1, zero_le_one, ?_⟩
      intro g q hg hq τ D x hτ hD hx he _
      have hgne : g x ≠ 0 := by intro hz; simp [hz] at hx; linarith
      have hqv : q x = (g x)⁻¹ := by
        calc
          q x = q x * g x * (g x)⁻¹ := by rw [mul_assoc,mul_inv_cancel₀ hgne,mul_one]
          _ = _ := by rw [he.eq_of_nhds,one_mul]
      simp only [iteratedDeriv_zero,hqv,abs_inv,pow_zero,mul_one,one_mul]
      exact (inv_le_inv₀ (lt_of_lt_of_le hτ hx) hτ).mpr hx
    | succ n =>
      let C₀ : ℕ → ℝ := fun k => if hk : k < n+1 then (ih k hk).choose else 0
      have hC₀ (k : ℕ) : 0 ≤ C₀ k := by
        dsimp [C₀]
        split_ifs with hk
        · exact (ih k hk).choose_spec.1
        · exact le_rfl
      let C := ∑ k ∈ Finset.range (n+1), ((n+1).choose k : ℝ) * C₀ k * B (n+1-k)
      have hC : 0 ≤ C := Finset.sum_nonneg (fun k _ =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC₀ k)) (hB _))
      refine ⟨C,hC,?_⟩
      intro g q hg hq τ D x hτ hD hx he hgb
      have hqfin : ContDiffAt ℝ (n+1 : ℕ) q x :=
        (hq.of_le (WithTop.coe_le_coe.mpr (show ((n+1 : ℕ) : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
      have hgfin : ContDiffAt ℝ (n+1 : ℕ) g x :=
        (hg.of_le (WithTop.coe_le_coe.mpr (show ((n+1 : ℕ) : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
      have hid := he.iteratedDeriv_eq (n+1)
      rw [iteratedDeriv_fun_mul hqfin hgfin, Finset.sum_range_succ] at hid
      simp only [Nat.choose_self,Nat.cast_one,one_mul,Nat.sub_self,iteratedDeriv_zero,
        iteratedDeriv_const,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceIte] at hid
      have hlast : iteratedDeriv (n+1) q x * g x =
          -(∑ k ∈ Finset.range (n+1), ((n+1).choose k : ℝ) *
            iteratedDeriv k q x * iteratedDeriv (n+1-k) g x) := by linarith
      have hsum : |iteratedDeriv (n+1) q x| * |g x| ≤ C * D^(n+1) := by
        rw [← abs_mul,hlast,abs_neg]
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        change _ ≤ (∑ k ∈ Finset.range (n+1), _) * _
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro k hk
        have hk' : k < n+1 := Finset.mem_range.mp hk
        have hqk := (ih k hk').choose_spec.2 g q hg hq τ D x hτ hD hx he
          (fun j hj hjk => hgb j hj (by omega))
        have hCk : C₀ k = (ih k hk').choose := dite_eq_left hk'
        rw [← hCk] at hqk
        rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
        calc
          _ ≤ ((n+1).choose k : ℝ) * (C₀ k * τ⁻¹ * D^k) *
              (B (n+1-k) * τ * D^(n+1-k)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hqk (Nat.cast_nonneg _))
              (hgb (n+1-k) (by omega) (by omega)) (abs_nonneg _)
              (mul_nonneg (Nat.cast_nonneg _)
                (mul_nonneg (mul_nonneg (hC₀ k) (inv_nonneg.mpr hτ.le)) (pow_nonneg hD k)))
          _ = ((n+1).choose k : ℝ) * C₀ k * B (n+1-k) * D^(n+1) := by
            have hpow : D^k * D^(n+1-k) = D^(n+1) := by
              rw [← pow_add, Nat.add_sub_of_le (by omega : k ≤ n+1)]
            calc
              _ = ((n+1).choose k : ℝ) * C₀ k * B (n+1-k) *
                  (τ⁻¹*τ) * (D^k*D^(n+1-k)) := by ring
              _ = _ := by rw [inv_mul_cancel₀ hτ.ne',mul_one,hpow]
      have hsmall : |iteratedDeriv (n+1) q x| * τ ≤ C * D^(n+1) :=
        (mul_le_mul_of_nonneg_left hx (abs_nonneg _)).trans hsum
      have hh := (le_div_iff₀ hτ).mpr hsmall
      simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ChartGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The failed perpendicular test in an actual spherical chart

The normalized affine chart stays within twice its tangent displacement
of the cap center. Its coordinate derivative therefore inherits the
uniform lower bound proved for the tangential sphere field.
-/

namespace Falconer
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem tangent_chart_nonzero {w h : E} (hw : ‖w‖ = 1) (hh : inner ℝ w h = 0) :
    w+h ≠ 0 := by
  intro he
  have hi := congrArg (inner ℝ w) he
  simp only [inner_add_right,real_inner_self_eq_norm_sq,hw,one_pow,hh,add_zero,
    inner_zero_right] at hi
  norm_num at hi

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_ChartDerivatives
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform derivatives of the normalized line chart

The scalar denominator is a smooth function of two real variables on a
fixed compact square. Its bounds are independent of the chart center,
tangent direction, and displacement. No analytic input is assumed here.
-/

namespace Falconer
open Set
open scoped ContDiff

private theorem partialSecond_smooth {F : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (n : ℕ) : ContDiff ℝ ∞ (partialSecond F n) := by
  induction n with
  | zero => exact hF
  | succ n ih =>
    exact (ih.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const

private theorem partialSecond_eq {F : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (n : ℕ) (s u : ℝ) :
    partialSecond F n (s,u) = iteratedDeriv n (fun x => F (s,x)) u := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    have hp : HasDerivAt (fun x : ℝ => (s,x)) (0,1) u :=
      (hasDerivAt_const u s).prodMk (hasDerivAt_id u)
    have hh := ((partialSecond_smooth hF n).differentiable (by simp) (s,u)).hasFDerivAt.comp_hasDerivAt u hp
    rw [iteratedDeriv_succ]
    change fderiv ℝ (partialSecond F n) (s,u) (0,1) = _
    rw [← hh.deriv]
    congr 1
    funext x
    exact ih x

private theorem uniform_section_derivatives {F : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (-1 : ℝ) 1, ∀ u ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv n (fun x => F (s,x)) u| ≤ C := by
  have hc := (partialSecond_smooth hF n).continuous.abs
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image hc.continuousOn
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro s hs u hu
  rw [← partialSecond_eq hF]
  exact (hC ⟨(s,u),⟨hs,hu⟩,rfl⟩).trans (le_max_left _ _)

theorem chartLineKernel_smooth : ContDiff ℝ ∞ chartLineKernel := by
  have h : ContDiff ℝ ∞ (fun p : ℝ × ℝ => 1+p.1^2+p.2^2) := by fun_prop
  exact (h.sqrt (fun p => by positivity)).inv (fun p => by positivity)

theorem chartLineKernel_derivatives (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (-1 : ℝ) 1, ∀ u ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv n (fun x => chartLineKernel (s,x)) u| ≤ C :=
  uniform_section_derivatives chartLineKernel_smooth n

theorem chartLineLinearKernel_derivatives (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (-1 : ℝ) 1, ∀ u ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv n (fun x => x * chartLineKernel (s,x)) u| ≤ C :=
  uniform_section_derivatives (contDiff_snd.mul chartLineKernel_smooth) n

section InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem tangent_line_norm_sq {w y t : E} (hw : ‖w‖ = 1) (ht : ‖t‖ = 1)
    (hwy : inner ℝ w y = 0) (hwt : inner ℝ w t = 0)
    (hyt : inner ℝ y t = 0) (u : ℝ) :
    ‖(w+y)+u•t‖^2 = 1+‖y‖^2+u^2 := by
  rw [norm_add_sq_real,norm_add_sq_real,inner_add_left,real_inner_smul_right,
    real_inner_smul_right,hwy,hwt,hyt,hw,norm_smul,ht,Real.norm_eq_abs]
  simp only [one_pow,mul_zero,zero_add,mul_one,sq_abs]
  ring

end InnerProduct

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ChartCoordinates
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalized line sections of the gnomonic chart

The first tangent coordinate is isolated exactly. The other coordinates
give a vector perpendicular to both the pole and the chosen tangent axis.
-/

namespace Falconer

theorem coordinateJoin_inner {n : ℕ} (x y : Space n) (u v : ℝ) :
    inner ℝ (coordinateJoin x u) (coordinateJoin y v) = u*v + inner ℝ x y := by
  rw [PiLp.inner_apply,PiLp.inner_apply,Fin.sum_univ_succ]
  simp [coordinateJoin_eq]
  ring

theorem coordinateJoin_norm_sq {n : ℕ} (x : Space n) (u : ℝ) :
    ‖coordinateJoin x u‖^2 = u^2+‖x‖^2 := by
  rw [← real_inner_self_eq_norm_sq,coordinateJoin_inner,real_inner_self_eq_norm_sq]
  ring

@[simp] theorem chartPole_norm (n : ℕ) : ‖chartPole n‖ = 1 := by
  have h := coordinateJoin_norm_sq (0 : Space (n+1)) 1
  norm_num at h
  dsimp [chartPole]
  rcases h with h | h
  · exact h
  · nlinarith [norm_nonneg (coordinateJoin (0 : Space (n+1)) 1)]

@[simp] theorem chartAxis_norm (n : ℕ) : ‖chartAxis n‖ = 1 := by
  have h₁ := coordinateJoin_norm_sq (0 : Space n) 1
  have h₂ := coordinateJoin_norm_sq (coordinateJoin (0 : Space n) 1) 0
  dsimp [chartAxis]
  norm_num at h₁ h₂
  rcases h₁ with h₁ | h₁
  · nlinarith
  · nlinarith [norm_nonneg (coordinateJoin (0 : Space n) 1)]

@[simp] theorem transverseLift_norm {n : ℕ} (x : Space n) : ‖transverseLift x‖ = ‖x‖ := by
  have h₁ := coordinateJoin_norm_sq x 0
  have h₂ := coordinateJoin_norm_sq (coordinateJoin x 0) 0
  dsimp [transverseLift]
  norm_num at h₁ h₂
  nlinarith [norm_nonneg (coordinateJoin (coordinateJoin x 0) 0),norm_nonneg x]

@[simp] theorem chartPole_inner_transverse {n : ℕ} (x : Space n) :
    inner ℝ (chartPole n) (transverseLift x) = 0 := by
  simp [chartPole,transverseLift,coordinateJoin_inner]

@[simp] theorem chartPole_inner_axis (n : ℕ) :
    inner ℝ (chartPole n) (chartAxis n) = 0 := by
  simp [chartPole,chartAxis,coordinateJoin_inner]

@[simp] theorem transverseLift_inner_axis {n : ℕ} (x : Space n) :
    inner ℝ (transverseLift x) (chartAxis n) = 0 := by
  simp [transverseLift,chartAxis,coordinateJoin_inner]

theorem northLift_coordinateJoin {n : ℕ} (x : Space n) (u : ℝ) :
    northLift (coordinateJoin x u) =
      (chartPole n + transverseLift x) + u • chartAxis n := by
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [northLift,chartPole,transverseLift,chartAxis,coordinateJoin_eq]
  · refine Fin.cases ?_ (fun k => ?_) j
    · simp [northLift,chartPole,transverseLift,chartAxis,coordinateJoin_eq]
    · simp [northLift,chartPole,transverseLift,chartAxis,coordinateJoin_eq]

theorem gnomonicChart_coordinateJoin {n : ℕ} (x : Space n) (u : ℝ) :
    (gnomonicChart (coordinateJoin x u) : Space (n+2)) =
      normalizedLine (chartPole n + transverseLift x) (chartAxis n) u := by
  simp only [gnomonicChart,normalizedLine,northLift_coordinateJoin]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_AmbientSymbols
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ambient smooth symbols in the adapted spherical chart

The smooth cap partition is constructed in Euclidean space. Its restriction
to every rotated one-coordinate spherical chart is smooth, including at
points where the amplitude vanishes.
-/

namespace Falconer
open Set
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem normalizedLine_contDiff (a t : E) (hne : ∀ u : ℝ, a+u•t ≠ 0) :
    ContDiff ℝ ∞ (normalizedLine a t) := by
  have hz : ContDiff ℝ ∞ (fun u : ℝ => a+u•t) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  exact ((hz.norm ℝ hne).inv (fun u => norm_ne_zero_iff.mpr (hne u))).smul hz

theorem ambient_symbol_chart_smooth {n : ℕ}
    (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (F : Space (n+2) → ℂ)
    (hF : ContDiff ℝ ∞ F) (y : Space n) :
    ContDiff ℝ ∞ (rotatedChartAmplitude e (fun w => F w) y) := by
  have hn (u : ℝ) : (chartPole n+transverseLift y)+u•chartAxis n ≠ 0 := by
    rw [add_assoc]
    apply tangent_chart_nonzero (chartPole_norm n)
    simp only [inner_add_right,real_inner_smul_right,chartPole_inner_transverse,
      chartPole_inner_axis,mul_zero,add_zero]
  have hp := normalizedLine_contDiff (chartPole n+transverseLift y) (chartAxis n) hn
  have he : ContDiff ℝ ∞ (fun x : Space (n+2) => e x) := e.toContinuousLinearMap.contDiff
  have hc := hF.comp (he.comp hp)
  change ContDiff ℝ ∞ (fun u => F (e (gnomonicChart (coordinateJoin y u))))
  simpa only [Function.comp_def,gnomonicChart_coordinateJoin] using hc

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_BumpDerivatives
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform derivatives of scaled cap bumps

A single compactly supported bump controls every center and radius. The
scale enters through the curve supplied to that fixed bump, so the k-th
bound loses only the k-th power of the inverse cap radius.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem capBump_eq_unit {d : ℕ} (δ : ℝ) (hδ : 0 < δ) (c : Sphere d) (x : Space d) :
    capBump δ hδ c x = unitCapBump d ((δ/2)⁻¹ • (x-(c : Space d))) := by
  have hr : δ/(δ/2) = 2 := by field_simp
  simp only [ContDiffBump.apply,capBump,unitCapBump,hr,div_one,inv_one,one_smul,sub_zero]

/-- This applies to an arbitrary smooth curve and will be specialized to the
rotated normalized line. The constant is independent of its center and scale. -/
theorem capBump_curve_derivatives (d m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
      ∀ (c : Sphere d) (γ : ℝ → Space d), ContDiff ℝ ∞ γ →
      ∀ (D u : ℝ), 1 ≤ D →
      (∀ k, 1 ≤ k → k ≤ m → ‖iteratedDeriv k γ u‖ ≤ D^k) →
      |iteratedDeriv m (fun t => capBump δ hδ c (γ t)) u| ≤ C*(D/δ)^m := by
  obtain ⟨B,hB,hBb⟩ := (unitCapBump d).hasCompactSupport.exists_bound_iteratedFDeriv
    (unitCapBump d).contDiff m
  refine ⟨(m.factorial : ℝ)*B*2^m,by positivity,?_⟩
  intro δ hδ hδ1 c γ hγ D u hD hγb
  let f : ℝ → Space d := fun t => (δ/2)⁻¹ • (γ t-(c : Space d))
  have hf : ContDiff ℝ ∞ f := by
    dsimp [f]
    exact (hγ.sub contDiff_const).const_smul _
  have hscale : 1 ≤ (δ/2)⁻¹ := (one_le_inv₀ (half_pos hδ)).mpr (by linarith)
  have hfb (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m) :
      ‖iteratedFDeriv ℝ k f u‖ ≤ ((δ/2)⁻¹*D)^k := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    change ‖iteratedDeriv k (fun t => (δ/2)⁻¹ • (γ t-(c : Space d))) u‖ ≤ _
    rw [iteratedDeriv_fun_const_smul_field,
      iteratedDeriv_fun_sub ((hγ.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt) contDiffAt_const,
      iteratedDeriv_const,ite_eq_right (by omega : k ≠ 0),sub_zero,norm_smul,
      Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (half_pos hδ))]
    calc
      _ ≤ (δ/2)⁻¹*D^k := mul_le_mul_of_nonneg_left (hγb k hk hkm) (by positivity)
      _ ≤ ((δ/2)⁻¹)^k*D^k := mul_le_mul_of_nonneg_right
        (le_self_pow₀ hscale (by omega)) (pow_nonneg (by linarith) _)
      _ = _ := (mul_pow _ _ _).symm
  have hh := norm_iteratedFDeriv_comp_le (unitCapBump d).contDiff hf
    (show (m : ℕ∞ω) ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) u (fun k hk => hBb k hk _) hfb
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hh
  have he : (unitCapBump d) ∘ f = (fun t => capBump δ hδ c (γ t)) := by
    funext t
    exact (capBump_eq_unit δ hδ c (γ t)).symm
  rw [he,Real.norm_eq_abs] at hh
  apply hh.trans_eq
  have hr : (δ/2)⁻¹*D = 2*(D/δ) := by field_simp
  rw [hr,mul_pow]
  ring

section InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem tangent_line_eq {w y t : E} (hw : ‖w‖ = 1) (ht : ‖t‖ = 1)
    (hwy : inner ℝ w y = 0) (hwt : inner ℝ w t = 0)
    (hyt : inner ℝ y t = 0) (u : ℝ) :
    normalizedLine (w+y) t u =
      chartLineKernel (‖y‖,u) • (w+y) + (u*chartLineKernel (‖y‖,u)) • t := by
  have hn : ‖(w+y)+u•t‖ = Real.sqrt (1+‖y‖^2+u^2) := by
    rw [← tangent_line_norm_sq hw ht hwy hwt hyt,Real.sqrt_sq (norm_nonneg _)]
  simp only [normalizedLine,hn,chartLineKernel,smul_add,smul_smul]
  rw [mul_comm]

theorem tangent_line_derivatives (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (w y t : E),
      ‖w‖ = 1 → ‖t‖ = 1 → inner ℝ w y = 0 → inner ℝ w t = 0 →
      inner ℝ y t = 0 → ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
      ‖iteratedDeriv m (normalizedLine (w+y) t) u‖ ≤ B := by
  obtain ⟨C,hC,hCb⟩ := chartLineKernel_derivatives m
  obtain ⟨D,hD,hDb⟩ := chartLineLinearKernel_derivatives m
  refine ⟨2*C+D,by positivity,?_⟩
  intro w y t hw ht hwy hwt hyt hy u hu
  have hys : ‖y‖ ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [norm_nonneg y],hy⟩
  have hk : ContDiff ℝ ∞ (fun x => chartLineKernel (‖y‖,x)) :=
    chartLineKernel_smooth.comp (contDiff_const.prodMk contDiff_id)
  have hl : ContDiff ℝ ∞ (fun x : ℝ => x*chartLineKernel (‖y‖,x)) :=
    contDiff_id.mul hk
  have hwyb : ‖w+y‖ ≤ 2 := (norm_add_le _ _).trans (by rw [hw]; linarith)
  have he : normalizedLine (w+y) t = (fun x =>
      chartLineKernel (‖y‖,x) • (w+y) + (x*chartLineKernel (‖y‖,x)) • t) :=
    funext (tangent_line_eq hw ht hwy hwt hyt)
  have hk' : ContDiff ℝ ∞ (fun x => chartLineKernel (‖y‖,x) • (w+y)) :=
    hk.smul contDiff_const
  have hl' : ContDiff ℝ ∞ (fun x => (x*chartLineKernel (‖y‖,x)) • t) :=
    hl.smul contDiff_const
  rw [he,iteratedDeriv_fun_add
    ((hk'.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt) ((hl'.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt),
    iteratedDeriv_smul_const ((hk.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt),
    iteratedDeriv_smul_const ((hl.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt)]
  calc
    _ ≤ ‖iteratedDeriv m (fun x => chartLineKernel (‖y‖,x)) u • (w+y)‖ +
        ‖iteratedDeriv m (fun x => x*chartLineKernel (‖y‖,x)) u • t‖ := norm_add_le _ _
    _ ≤ C*2+D*1 := by
      simp only [norm_smul,Real.norm_eq_abs]
      exact add_le_add (mul_le_mul (hCb _ hys _ hu) hwyb (norm_nonneg _) hC)
        (mul_le_mul (hDb _ hys _ hu) ht.le (norm_nonneg _) hD)
    _ = _ := by ring

/-- One fixed scale controls all positive orders up to a chosen finite order. -/
theorem tangent_line_derivative_scale (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (w y t : E),
      ‖w‖ = 1 → ‖t‖ = 1 → inner ℝ w y = 0 → inner ℝ w t = 0 →
      inner ℝ y t = 0 → ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
      ∀ k, 1 ≤ k → k ≤ m → ‖iteratedDeriv k (normalizedLine (w+y) t) u‖ ≤ D^k := by
  choose B hB hBb using (fun k => tangent_line_derivatives (E := E) k)
  let D := 1+∑ k ∈ Finset.range (m+1), B k
  have hD : 1 ≤ D := by
    dsimp [D]
    linarith [Finset.sum_nonneg (fun k (_ : k ∈ Finset.range (m+1)) => hB k)]
  refine ⟨D,hD,?_⟩
  intro w y t hw ht hwy hwt hyt hy u hu k hk hkm
  apply (hBb k w y t hw ht hwy hwt hyt hy u hu).trans
  have hb : B k ≤ D := by
    have hsum := Finset.single_le_sum (fun j (_ : j ∈ Finset.range (m+1)) => hB j)
      (Finset.mem_range.mpr (by omega : k < m+1))
    dsimp [D]
    linarith
  exact hb.trans (le_self_pow₀ hD (by omega))

end InnerProduct
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_ChartBumps
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cap bump derivatives in every rotated spherical chart

The constants depend only on the ambient dimension and derivative order.
The cap center, rotation, radius and transverse chart coordinate remain free.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem rotatedChartCurve_contDiff {n : ℕ}
    (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (y : Space n) :
    ContDiff ℝ ∞ (rotatedChartCurve e y) := by
  have hn (u : ℝ) : (chartPole n+transverseLift y)+u•chartAxis n ≠ 0 := by
    rw [add_assoc]
    apply tangent_chart_nonzero (chartPole_norm n)
    simp only [inner_add_right,real_inner_smul_right,chartPole_inner_transverse,
      chartPole_inner_axis,mul_zero,add_zero]
  have hp := normalizedLine_contDiff (chartPole n+transverseLift y) (chartAxis n) hn
  have he : ContDiff ℝ ∞ (fun x : Space (n+2) => e x) := e.toContinuousLinearMap.contDiff
  change ContDiff ℝ ∞ (fun u => e (gnomonicChart (coordinateJoin y u)))
  simpa only [Function.comp_def,gnomonicChart_coordinateJoin] using he.comp hp

theorem capBump_rotated_derivatives (n m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
      ∀ (c : Sphere (n+2)) (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2))
      (y : Space n), ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv m (fun t => capBump δ hδ c (rotatedChartCurve e y t)) u| ≤
        B*(δ⁻¹)^m := by
  obtain ⟨D,hD,hDb⟩ := tangent_line_derivative_scale (E := Space (n+2)) m
  obtain ⟨C,hC,hCb⟩ := capBump_curve_derivatives (n+2) m
  refine ⟨C*D^m,by positivity,?_⟩
  intro δ hδ hδ1 c e y hy u hu
  have hp : ∀ k, 1 ≤ k → k ≤ m → ‖iteratedDeriv k (rotatedChartCurve e y) u‖ ≤ D^k := by
    intro k hk hkm
    have he : rotatedChartCurve e y = e ∘
        normalizedLine (chartPole n+transverseLift y) (chartAxis n) := by
      funext t
      simp only [rotatedChartCurve,Function.comp_def,gnomonicChart_coordinateJoin]
    rw [he,← norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      e.norm_iteratedFDeriv_comp_left,norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hDb _ _ _ (chartPole_norm n) (chartAxis_norm n)
      (chartPole_inner_transverse y) (chartPole_inner_axis n) (transverseLift_inner_axis y)
      (by simpa only [transverseLift_norm] using hy) u hu k hk hkm
  have hh := hCb δ hδ hδ1 c (rotatedChartCurve e y) (rotatedChartCurve_contDiff e y)
    D u hD hp
  apply hh.trans_eq
  simp only [div_eq_mul_inv,mul_pow]
  ring

theorem capBump_rotated_derivative_zero {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (c : Sphere (n+2)) (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2))
    (y : Space n) (u : ℝ) (hfar : δ < ‖rotatedChartCurve e y u-(c : Space (n+2))‖)
    (m : ℕ) :
    iteratedDeriv m (fun t => capBump δ hδ c (rotatedChartCurve e y t)) u = 0 := by
  have hn : rotatedChartCurve e y u ∉ tsupport (capBump δ hδ c) := by
    rw [(capBump δ hδ c).tsupport_eq]
    exact not_le.mpr hfar
  have he := (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto
    (rotatedChartCurve_contDiff e y).continuous.continuousAt
  have hh := he.iteratedDeriv_eq m
  simpa only [Function.comp_def,Pi.zero_apply,iteratedDeriv_const,ite_self] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CapDenominator
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform bounds for the cap partition denominator

Only centers whose closed cap contains the point contribute to a derivative.
The proved local packing bound therefore controls the sum independently of
the total number of caps.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem capDenominator_ge_one {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2) (w : Sphere d) :
    1 ≤ capDenominator δ hδ S w := by
  obtain ⟨c,hc,hwc⟩ := hcover w
  have hval : capBump δ hδ c w = 1 :=
    (capBump δ hδ c).one_of_mem_closedBall (Metric.mem_closedBall.mpr hwc)
  calc
    1 = capBump δ hδ c w := hval.symm
    _ ≤ capDenominator δ hδ S w :=
      Finset.single_le_sum (fun c _ => (capBump δ hδ c).nonneg) hc

theorem capDenominator_chart_derivatives (n m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
      ∀ (S : Finset (Sphere (n+2))),
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 ≤ dist x y) →
      ∀ (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (y : Space n), ‖y‖ ≤ 1 →
      ∀ u ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv m (fun t => capDenominator δ hδ S (rotatedChartCurve e y t)) u| ≤
        B*(δ⁻¹)^m := by
  classical
  obtain ⟨C,hC,hCb⟩ := capBump_rotated_derivatives n m
  refine ⟨5^(n+2)*C,by positivity,?_⟩
  intro δ hδ hδ1 S hsep e y hy u hu
  let w : Sphere (n+2) := sphereMap e (gnomonicChart (coordinateJoin y u))
  let T := S.filter (fun c => dist w c ≤ δ)
  let f : Sphere (n+2) → ℝ := fun c =>
    iteratedDeriv m (fun t => capBump δ hδ c (rotatedChartCurve e y t)) u
  have hdiff (c : Sphere (n+2)) :
      ContDiff ℝ ∞ (fun t => capBump δ hδ c (rotatedChartCurve e y t)) :=
    (capBump δ hδ c).contDiff.comp (rotatedChartCurve_contDiff e y)
  have hzero (c : Sphere (n+2)) (hc : c ∈ S) (hct : c ∉ T) : f c = 0 := by
    have hdist : δ < dist w c := lt_of_not_ge (fun h => hct (Finset.mem_filter.mpr ⟨hc,h⟩))
    exact capBump_rotated_derivative_zero hδ c e y u hdist m
  have hsum : (∑ c ∈ S, f c) = ∑ c ∈ T, f c := by
    symm
    exact Finset.sum_subset (Finset.filter_subset _ _) hzero
  change |iteratedDeriv m (fun t => ∑ c ∈ S, capBump δ hδ c (rotatedChartCurve e y t)) u| ≤ _
  rw [iteratedDeriv_fun_sum (fun c _ => ((hdiff c).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt)]
  change |∑ c ∈ S, f c| ≤ _
  rw [hsum]
  calc
    _ ≤ ∑ c ∈ T, |f c| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c ∈ T, C*(δ⁻¹)^m := Finset.sum_le_sum (fun c _ => hCb δ hδ hδ1 c e y hy u hu)
    _ = (T.card : ℝ)*(C*(δ⁻¹)^m) := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ 5^(n+2)*(C*(δ⁻¹)^m) := mul_le_mul_of_nonneg_right
      (separated_sphere_overlap S hδ hsep w) (by positivity)
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CapReciprocal
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Derivatives of the cap normalization factor -/

namespace Falconer
open Set
open scoped ContDiff Topology

theorem capDenominator_mul_reciprocal {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2) (w : Sphere d) :
    capDenominator δ hδ S w * capReciprocal δ hδ S w = 1 := by
  exact smoothReciprocal_eq zero_lt_one
    ((capDenominator_ge_one hδ S hcover w).trans (le_abs_self _))

theorem capReciprocal_chart_derivatives (n m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
      ∀ (S : Finset (Sphere (n+2))),
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 ≤ dist x y) →
      (∀ w : Sphere (n+2), ∃ c ∈ S, dist w c ≤ δ/2) →
      ∀ (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (y : Space n), ‖y‖ ≤ 1 →
      ∀ u ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv m (fun t => capReciprocal δ hδ S (rotatedChartCurve e y t)) u| ≤
        B*(δ⁻¹)^m := by
  choose B hB hBb using (fun k => capDenominator_chart_derivatives n k)
  obtain ⟨C,hC,hCb⟩ := reciprocal_germ_derivatives B hB m
  refine ⟨C,hC,?_⟩
  intro δ hδ hδ1 S hsep hcover e y hy u hu
  let g : ℝ → ℝ := fun t => capDenominator δ hδ S (rotatedChartCurve e y t)
  let q : ℝ → ℝ := fun t => capReciprocal δ hδ S (rotatedChartCurve e y t)
  have hg : ContDiff ℝ ∞ g := (capDenominator_contDiff hδ S).comp (rotatedChartCurve_contDiff e y)
  have hq : ContDiff ℝ ∞ q := (capReciprocal_contDiff hδ S).comp (rotatedChartCurve_contDiff e y)
  have hw (t : ℝ) : rotatedChartCurve e y t ∈ Metric.sphere (0 : Space (n+2)) 1 := by
    simp only [Metric.mem_sphere,dist_zero_right,rotatedChartCurve_norm]
  have hg1 (t : ℝ) : 1 ≤ g t := capDenominator_ge_one hδ S hcover ⟨_,hw t⟩
  have he : (fun t => q t*g t) =ᶠ[𝓝 u] (fun _ => 1) := Filter.Eventually.of_forall (by
    intro t
    simpa only [g,q,mul_comm] using capDenominator_mul_reciprocal hδ S hcover ⟨_,hw t⟩)
  have hh := hCb g q hg hq 1 δ⁻¹ u zero_lt_one (inv_nonneg.mpr hδ.le)
    ((hg1 u).trans (le_abs_self _)) he (by
      intro k _hk _hkm
      simpa only [mul_one] using hBb k δ hδ hδ1 S hsep e y hy u hu)
  simpa only [inv_one,mul_one] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_NormalizedCaps
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The normalized cap partition and its uniform derivative bounds

The normalization uses the same fixed smooth reciprocal for all radii.
On the sphere the covering bound makes it the exact reciprocal of the
positive bump sum.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem normalizedCap_properties {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2) :
    (∀ w : Sphere d, ∑ c ∈ S, normalizedCap δ hδ S c w = 1) ∧
    (∀ c ∈ S, ∀ w : Sphere d, 0 ≤ normalizedCap δ hδ S c w ∧
      normalizedCap δ hδ S c w ≤ 1) ∧
    (∀ c ∈ S, ∀ x : Space d, normalizedCap δ hδ S c x ≠ 0 → ‖x-(c : Space d)‖ ≤ δ) := by
  have hrec (w : Sphere d) : capReciprocal δ hδ S w = (capDenominator δ hδ S w)⁻¹ := by
    have hg : capDenominator δ hδ S w ≠ 0 :=
      ne_of_gt (zero_lt_one.trans_le (capDenominator_ge_one hδ S hcover w))
    apply mul_left_cancel₀ hg
    rw [capDenominator_mul_reciprocal hδ S hcover w,mul_inv_cancel₀ hg]
  refine ⟨?_,?_,?_⟩
  · intro w
    simpa only [normalizedCap,← Finset.sum_mul,capDenominator] using
      capDenominator_mul_reciprocal hδ S hcover w
  · intro c hc w
    have hb : capBump δ hδ c w ≤ capDenominator δ hδ S w :=
      Finset.single_le_sum (fun c _ => (capBump δ hδ c).nonneg) hc
    have hg : 0 < capDenominator δ hδ S w :=
      zero_lt_one.trans_le (capDenominator_ge_one hδ S hcover w)
    simp only [normalizedCap,hrec]
    exact ⟨mul_nonneg (capBump δ hδ c).nonneg (inv_nonneg.mpr hg.le),
      (mul_inv_le_iff₀ hg).mpr (by simpa only [one_mul] using hb)⟩
  · intro c _ x hx
    have hb : capBump δ hδ c x ≠ 0 := (mul_ne_zero_iff.mp hx).1
    have hm : x ∈ Metric.ball (c : Space d) δ := by
      change x ∈ Metric.ball (c : Space d) (capBump δ hδ c).rOut
      rw [← (capBump δ hδ c).support_eq]
      exact hb
    exact (mem_ball_iff_norm.mp hm).le

theorem normalizedCap_chart_derivatives (n m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
      ∀ (S : Finset (Sphere (n+2))),
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 ≤ dist x y) →
      (∀ w : Sphere (n+2), ∃ c ∈ S, dist w c ≤ δ/2) →
      ∀ (c : Sphere (n+2)) (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2))
      (y : Space n), ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv m (fun t => normalizedCap δ hδ S c (rotatedChartCurve e y t)) u| ≤
        B*(δ⁻¹)^m := by
  choose B hB hBb using (fun k => capBump_rotated_derivatives n k)
  choose Q hQ hQb using (fun k => capReciprocal_chart_derivatives n k)
  let A := ∑ k ∈ Finset.range (m+1), (m.choose k : ℝ)*B k*Q (m-k)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun k _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB k)) (hQ (m-k)))
  refine ⟨A,hA,?_⟩
  intro δ hδ hδ1 S hsep hcover c e y hy u hu
  have hb : ContDiff ℝ ∞ (fun t => capBump δ hδ c (rotatedChartCurve e y t)) :=
    (capBump δ hδ c).contDiff.comp (rotatedChartCurve_contDiff e y)
  have hq : ContDiff ℝ ∞ (fun t => capReciprocal δ hδ S (rotatedChartCurve e y t)) :=
    (capReciprocal_contDiff hδ S).comp (rotatedChartCurve_contDiff e y)
  change |iteratedDeriv m (fun t => capBump δ hδ c (rotatedChartCurve e y t)*
    capReciprocal δ hδ S (rotatedChartCurve e y t)) u| ≤ _
  rw [iteratedDeriv_fun_mul ((hb.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt) ((hq.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt)]
  calc
    _ ≤ ∑ k ∈ Finset.range (m+1), |(m.choose k : ℝ)*
        iteratedDeriv k (fun t => capBump δ hδ c (rotatedChartCurve e y t)) u*
        iteratedDeriv (m-k) (fun t => capReciprocal δ hδ S (rotatedChartCurve e y t)) u| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (m+1), ((m.choose k : ℝ)*B k*Q (m-k))*(δ⁻¹)^m := by
      apply Finset.sum_le_sum
      intro k hk
      have hkm : k ≤ m := by have := Finset.mem_range.mp hk; omega
      rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
      calc
        _ ≤ (m.choose k : ℝ)*(B k*(δ⁻¹)^k)*(Q (m-k)*(δ⁻¹)^(m-k)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hBb k δ hδ hδ1 c e y hy u hu)
            (Nat.cast_nonneg _)) (hQb (m-k) δ hδ hδ1 S hsep hcover e y hy u hu)
            (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
              (mul_nonneg (hB k) (pow_nonneg (inv_nonneg.mpr hδ.le) k)))
        _ = _ := by
          have hp : (δ⁻¹)^k*(δ⁻¹)^(m-k) = (δ⁻¹)^m := by
            rw [← pow_add,Nat.add_sub_of_le hkm]
          calc
            _ = ((m.choose k : ℝ)*B k*Q (m-k))*((δ⁻¹)^k*(δ⁻¹)^(m-k)) := by ring
            _ = _ := by rw [hp]
    _ = A*(δ⁻¹)^m := (Finset.sum_mul _ _ _).symm

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_QuantitativeCaps
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quantitative smooth cap partition on the sphere

This supplies the actual partition used in angular localization, with
uniform derivatives, a polynomial global count, and bounded local overlap.
It contains no Fourier or incidence estimate as an assumption.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem normalizedCap_complex_chart_derivatives (n m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
      ∀ (S : Finset (Sphere (n+2))),
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 ≤ dist x y) →
      (∀ w : Sphere (n+2), ∃ c ∈ S, dist w c ≤ δ/2) →
      ∀ (c : Sphere (n+2)) (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2))
      (y : Space n), ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
      ‖iteratedDeriv m (rotatedChartAmplitude e
        (fun w => (normalizedCap δ hδ S c w : ℂ)) y) u‖ ≤ B*(δ⁻¹)^m := by
  obtain ⟨B,hB,hBb⟩ := normalizedCap_chart_derivatives n m
  refine ⟨B,hB,?_⟩
  intro δ hδ hδ1 S hsep hcover c e y hy u hu
  let f : ℝ → ℝ := fun t => normalizedCap δ hδ S c (rotatedChartCurve e y t)
  have hf : ContDiff ℝ ∞ f :=
    (normalizedCap_contDiff hδ S c).comp (rotatedChartCurve_contDiff e y)
  have hn := Complex.ofRealLI.norm_iteratedFDeriv_comp_left (hf.contDiffAt (x := u))
    (show (m : ℕ∞ω) ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    Real.norm_eq_abs] at hn
  change ‖iteratedDeriv m (Complex.ofRealLI ∘ f) u‖ ≤ _
  rw [hn]
  exact hBb δ hδ hδ1 S hsep hcover c e y hy u hu

theorem quantitative_smooth_cap_partition (n m : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∃ (S : Finset (Sphere (n+2))) (η : Sphere (n+2) → Sphere (n+2) → ℝ),
        (S.card : ℝ) ≤ (4/δ+1)^(n+2) ∧
        (∀ w, ((S.filter (fun c => dist w c ≤ δ)).card : ℝ) ≤ (5 : ℝ)^(n+2)) ∧
        (∀ c, Measurable (η c)) ∧
        (∀ w, ∑ c ∈ S, η c w = 1) ∧
        (∀ c ∈ S, ∀ w, 0 ≤ η c w ∧ η c w ≤ 1) ∧
        (∀ c ∈ S, ∀ w, η c w ≠ 0 → ‖(w : Space (n+2))-(c : Space (n+2))‖ ≤ δ) ∧
        (∀ c, ∀ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), ∀ y : Space n,
          ContDiff ℝ ∞ (rotatedChartAmplitude e (fun w => (η c w : ℂ)) y)) ∧
        (∀ c, ∀ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), ∀ y : Space n, ‖y‖ ≤ 1 →
          ∀ u ∈ Icc (-1 : ℝ) 1, ∀ k ≤ m,
          ‖iteratedDeriv k (rotatedChartAmplitude e (fun w => (η c w : ℂ)) y) u‖ ≤ H*(δ⁻¹)^k) := by
  classical
  choose B hB hBb using (fun k => normalizedCap_complex_chart_derivatives n k)
  let H := ∑ k ∈ Finset.range (m+1), B k
  have hH : 0 ≤ H := Finset.sum_nonneg (fun k _ => hB k)
  refine ⟨H,hH,?_⟩
  intro δ hδ hδ1
  obtain ⟨S,hsep,hcover,hcard,hoverlap⟩ := finite_separated_cap_net (n+2) hδ
  obtain ⟨hpart,hbounds,hsupport⟩ := normalizedCap_properties hδ S hcover
  refine ⟨S,fun c w => normalizedCap δ hδ S c w,hcard,hoverlap,?_,hpart,hbounds,
    (fun c hc w => hsupport c hc w),?_,?_⟩
  · intro c
    exact (normalizedCap_contDiff hδ S c).continuous.measurable.comp continuous_subtype_val.measurable
  · intro c e y
    exact ambient_symbol_chart_smooth e (fun x => (normalizedCap δ hδ S c x : ℂ))
      (Complex.ofRealCLM.contDiff.comp (normalizedCap_contDiff hδ S c)) y
  · intro c e y hy u hu k hkm
    apply (hBb k δ hδ hδ1 S (fun x hx y hy hxy => (hsep x hx y hy hxy).le)
      hcover c e y hy u hu).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact Finset.single_le_sum (fun j _ => hB j) (Finset.mem_range.mpr (by omega))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_DyadicCube
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dyadic cubes in the ambient dimension of the manuscript

Half-open cubes partition without boundary overlaps. Their centers and
Euclidean diameter bounds use the same original ambient coordinates as the
distance measure.
-/

namespace Falconer
open Set MeasureTheory

theorem DyadicCube.measurable {d : ℕ} (Q : DyadicCube d) : MeasurableSet Q.carrier := by
  simp only [carrier, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_le measurable_const (EuclideanSpace.proj i).continuous.measurable).inter
    (measurableSet_lt (EuclideanSpace.proj i).continuous.measurable measurable_const)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicTree
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite dyadic trees in the original ambient dimension

All descendants use half-open carriers. Equal-depth cells are disjoint and
partition the parent, so restriction to them is an exact measure splitting.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem card_cubePaths (d n : ℕ) : (cubePaths d n).card = 2^(d*n) := by
  induction n with
  | zero => simp [cubePaths]
  | succ n ih =>
    rw [cubePaths, Finset.card_biUnion]
    · have hc (b : Fin d → Bool) : Function.Injective (List.cons b) :=
        fun _ _ h => (List.cons.inj h).2
      simp only [Finset.card_image_of_injective _ (hc _), ih,
        Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, smul_eq_mul]
      rw [Nat.mul_succ, pow_add]
      exact Nat.mul_comm _ _
    · intro b _ c _ hbc
      apply Finset.disjoint_left.mpr
      intro p hp hq
      obtain ⟨p', _, hp'⟩ := Finset.mem_image.mp hp
      obtain ⟨q', _, hq'⟩ := Finset.mem_image.mp hq
      exact hbc (List.cons.inj (hp'.trans hq'.symm)).1

theorem DyadicCube.card_occupiedPaths_le {d : ℕ} (Q : DyadicCube d)
    (μ : Measure (Space d)) (n : ℕ) :
    (Q.occupiedPaths μ n).card ≤ 2^(d*n) := by
  rw [← card_cubePaths]
  exact Finset.card_filter_le _ _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_ChartSymbolControl
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite derivative data for the graph localization

These records express cap and endpoint regularity bounds. They contain no oscillatory estimate or incidence conclusion.
Spatial cell indicators preserve all the required angular derivative bounds.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

/-- The finite cap partition supplies the cap regularity bounds. -/
theorem exists_controlled_cap_partition (n m : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∃ (S : Finset (Sphere (n+2))) (η : Sphere (n+2) → Sphere (n+2) → ℝ),
        (S.card : ℝ) ≤ (4/δ+1)^(n+2) ∧
        (∀ w, ∑ c ∈ S, η c w = 1) ∧
        (∀ c ∈ S, ∀ w, 0 ≤ η c w) ∧
        ∀ c ∈ S, ChartCapControl m (η c) (c : Space (n+2)) δ H := by
  obtain ⟨H,hH,hmain⟩ := quantitative_smooth_cap_partition n m
  refine ⟨H,hH,?_⟩
  intro δ hδ hδ1
  obtain ⟨S,η,hcard,_hoverlap,hmeas,hpart,hbound,hsupp,hsmooth,hder⟩ := hmain δ hδ hδ1
  refine ⟨S,η,hcard,hpart,(fun c hc w => (hbound c hc w).1),?_⟩
  intro c hc
  refine ⟨hmeas c,?_,hsupp c hc,hsmooth c,?_⟩
  · intro w
    rw [abs_of_nonneg (hbound c hc w).1]
    exact (hbound c hc w).2
  · intro e k hk y hy u hu
    exact hder c e y hy u hu k hk

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_SpatialSymbols
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Spatial Fourier factors preserve angular symbol control -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem ChartSymbolControl.spatialMultiplier {n m : ℕ}
    {b : Space (n+2) → Sphere (n+2) → ℂ} {B D : ℝ}
    (h : ChartSymbolControl m b B D)
    (c : Space (n+2) → ℂ) (hc : Measurable c) (hcb : ∀ x, ‖c x‖ ≤ 1) :
    ChartSymbolControl m (fun x w => c x*b x w) B D := by
  refine ⟨(hc.comp measurable_fst).mul h.measurable,?_,?_,?_⟩
  · intro x w
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hcb x) (norm_nonneg _)).trans
      (by simpa only [one_mul] using h.bound x w)
  · intro x e y
    have he : rotatedChartAmplitude e (fun w => c x*b x w) y =
        fun u => c x*rotatedChartAmplitude e (b x) y u := rfl
    rw [he]
    exact contDiff_const.mul (h.smooth x e y)
  · intro e k hk x y hy u hu
    have he : rotatedChartAmplitude e (fun w => c x*b x w) y =
        fun u => c x*rotatedChartAmplitude e (b x) y u := rfl
    rw [he,iteratedDeriv_const_mul (c x) ((h.smooth x e y).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt,
      norm_mul]
    exact (mul_le_mul_of_nonneg_right (hcb x) (norm_nonneg _)).trans
      (by simpa only [one_mul] using h.derivative e k hk x y hy u hu)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_AmbientChartBudget
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ambient symbol bounds imply the ordinary rotated chart bounds

Only derivatives of the original symbol evaluated at sphere points are
used. The one-coordinate curve has a fixed, rotation-independent budget.
-/

namespace Falconer
open Set Metric
open scoped ContDiff

theorem rotatedChartCurve_derivative_scale (n K : ℕ) :
    ∃ q : ℝ, 1 ≤ q ∧ ∀ (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2))
      (y : Space n), ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
      ∀ k, 1 ≤ k → k ≤ K →
        ‖iteratedFDeriv ℝ k (rotatedChartCurve e y) u‖ ≤ q^k := by
  obtain ⟨q,hq,hqb⟩ := tangent_line_derivative_scale (E := Space (n+2)) K
  refine ⟨q,hq,?_⟩
  intro e y hy u hu k hk hkK
  have he : rotatedChartCurve e y = e ∘
      normalizedLine (chartPole n+transverseLift y) (chartAxis n) := by
    funext t
    simp only [rotatedChartCurve,Function.comp_def,gnomonicChart_coordinateJoin]
  rw [he,e.norm_iteratedFDeriv_comp_left,norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact hqb _ _ _ (chartPole_norm n) (chartAxis_norm n)
    (chartPole_inner_transverse y) (chartPole_inner_axis n) (transverseLift_inner_axis y)
    (by simpa only [transverseLift_norm] using hy) u hu k hk hkK

theorem ambient_symbol_rotated_chart_budget (n K : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ B : Space (n+2) → ℂ,
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ j ≤ K, ∀ w : Sphere (n+2), ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (y : Space n), ‖y‖ ≤ 1 →
      ∀ u ∈ Icc (-1 : ℝ) 1, ∀ k ≤ K,
        ‖iteratedDeriv k (rotatedChartAmplitude e (fun w => B w) y) u‖ ≤ H*C*D^k := by
  obtain ⟨q,hq,hqb⟩ := rotatedChartCurve_derivative_scale n K
  let a : ℕ → ℝ := fun k => mixedCompositionBudget (fun _ => 1) k*q^k
  have ha (k : ℕ) : 0 ≤ a k := mul_nonneg
    (mixedCompositionBudget_nonneg (fun _ => zero_le_one) k)
    (pow_nonneg (zero_le_one.trans hq) k)
  let H := ∑ k ∈ Finset.range (K+1), a k
  have hH : 0 ≤ H := Finset.sum_nonneg (fun k _ => ha k)
  refine ⟨H,hH,?_⟩
  intro B hB C D hC hD hb e y hy u hu k hk
  let w : Sphere (n+2) := ⟨rotatedChartCurve e y u,by
    rw [mem_sphere,dist_zero_right,rotatedChartCurve_norm]⟩
  have hCE : 0 ≤ C*D^k := mul_nonneg hC (pow_nonneg (zero_le_one.trans hD) k)
  have hh := mixed_composition_derivative_bound (B := fun _ => 1) (D := q)
    (rotatedChartCurve_contDiff e y).contDiffAt hB.contDiffAt hCE k
    (fun j hj => (hb j (hj.trans hk) w).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hD hj) hC))
    (fun j hj hjk => by simpa only [one_mul] using hqb e y hy u hu j hj (hjk.trans hk))
  have he : rotatedChartAmplitude e (fun w => B w) y = B ∘ rotatedChartCurve e y := rfl
  rw [he,← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  apply hh.trans
  have haH : a k ≤ H := Finset.single_le_sum (fun i _ => ha i)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  calc
    _ = a k*C*D^k := by dsimp [a]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right haH hC)
      (pow_nonneg (zero_le_one.trans hD) k)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_NormalizedInverseFactors
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Size-one endpoint factors with the exact total derivative cost

Positive upper sizes are selected before the scale label. Division by
those sizes retains all zero sets and chart bounds; their product costs
only the sum of the original endpoint derivative orders.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

theorem normalizedEndpoint_ne_zero {d : ℕ} (a : ℝ)
    (b : Space d → Sphere d → ℂ) (x : Space d) (w : Sphere d)
    (h : normalizedEndpoint a b x w ≠ 0) : b x w ≠ 0 :=
  (mul_ne_zero_iff.mp h).2

theorem ChartSymbolControl.normalized {n K : ℕ}
    {b : Space (n+2) → Sphere (n+2) → ℂ} {B D a : ℝ}
    (h : ChartSymbolControl K b B D) (ha : 0 < a) (hBa : B ≤ a) (hD : 0 ≤ D) :
    ChartSymbolControl K (normalizedEndpoint a b) 1 D := by
  have hn : ‖(a⁻¹ : ℝ)‖ = a⁻¹ := Real.norm_of_nonneg (inv_nonneg.mpr ha.le)
  refine ⟨measurable_const.mul h.measurable,?_,?_,?_⟩
  · intro x w
    simp only [normalizedEndpoint,norm_mul,Complex.norm_real,hn]
    exact (mul_le_mul_of_nonneg_left ((h.bound x w).trans hBa)
      (inv_nonneg.mpr ha.le)).trans_eq (inv_mul_cancel₀ ha.ne')
  · intro x e y
    exact contDiff_const.mul (h.smooth x e y)
  · intro e k hk x y hy u hu
    change ‖iteratedDeriv k (fun v => (a⁻¹ : ℝ)*rotatedChartAmplitude e (b x) y v) u‖ ≤ _
    rw [iteratedDeriv_const_mul _ ((h.smooth x e y).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt,
      norm_mul,Complex.norm_real,hn]
    calc
      _ ≤ a⁻¹*(B*D^k) := mul_le_mul_of_nonneg_left
        (h.derivative e k hk x y hy u hu) (inv_nonneg.mpr ha.le)
      _ ≤ a⁻¹*(a*D^k) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hBa (pow_nonneg hD _)) (inv_nonneg.mpr ha.le)
      _ = 1*D^k := by rw [← mul_assoc,inv_mul_cancel₀ ha.ne']

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularEnvelope
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A bounded supremum of the actual admissible endpoint energies

The admissible class records only the existing chart-symbol control and
the required support. Its envelope is the real supremum of the original
endpoint-transform energies, with zero inserted to ensure nonemptiness.
-/

namespace Falconer
open Set MeasureTheory

theorem AngularAdmissible.spatialMultiplier {n k : ℕ} {D : ℝ}
    {Good : Set (Space (n+2) × Sphere (n+2))}
    {b : Space (n+2) → Sphere (n+2) → ℂ} (h : AngularAdmissible k D Good b)
    (c : Space (n+2) → ℂ) (hc : Measurable c) (hcb : ∀ x, ‖c x‖ ≤ 1) :
    AngularAdmissible k D Good (fun x w => c x*b x w) :=
  ⟨h.1.spatialMultiplier c hc hcb,fun x w hw => h.2 x w (mul_ne_zero_iff.mp hw).2⟩

theorem AngularAdmissible.mono {n k : ℕ} {D E : ℝ}
    {Good Good' : Set (Space (n+2) × Sphere (n+2))}
    {b : Space (n+2) → Sphere (n+2) → ℂ}
    (h : AngularAdmissible k D Good b) (hD : 0 ≤ D) (hDE : D ≤ E)
    (hGood : Good ⊆ Good') : AngularAdmissible k E Good' b := by
  refine ⟨⟨h.1.measurable,h.1.bound,h.1.smooth,?_⟩,fun x w hw => hGood (h.2 x w hw)⟩
  intro e l hl x y hy u hu
  exact (h.1.derivative e l hl x y hy u hu).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hD hDE l) (by norm_num : (0:ℝ) ≤ 1))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_GraphNormalization
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dimension-dependent normalization and branch ledger

The critical slope is `d / 2`. Both copies of a profile are needed for
the cancellation of the spatial normalization. The last-potential bound
uses the last interval with a defined two-depth potential, even when the
final interval itself is shorter.
-/

namespace Falconer
open scoped BigOperators

theorem dyadic_rpow_change_base {N : ℕ} (hN : 0 < N) (x : ℝ) :
    ((2 : ℝ)^N) ^ (x / (N : ℝ)) = (2 : ℝ)^x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorMasks
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual anchored masks and retained pair tests in every dimension

The angular set at an anchor is tested against the full conditional law.
Masks use finite spherical nets at one eighth of the manuscript's buffer
radius. Their construction is independent of the number of anchor cells.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff Topology
open PlanarFalconer (PolicyDescriptor descriptorAnchor descriptorLength)
variable {d : ℕ}

theorem descriptorEndpointGood_on_cell (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (p : List (Fin d → Bool)) (hp : p.length = descriptorAnchor b)
    {x : Space d} (hx : x ∈ (Q.descendant p).carrier) (w : Sphere d) :
    (x,w) ∈ descriptorEndpointGood Q ρ m N σ J i b ↔
      w ∈ descriptorGoodDirections Q ρ m N σ J i p b := by
  constructor
  · exact fun h => h p ((mem_cubePaths _ _ _).mpr hp) hx
  · intro hw q hq hxq
    have hqp : q = p := by
      by_contra hn
      exact Set.disjoint_left.mp
        (Q.descendants_disjoint (((mem_cubePaths _ _ _).mp hq).trans hp.symm) hn) hxq hx
    simpa only [hqp] using hw

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SuffixScales
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The suffix scale hypotheses in the manuscript's separated geometry -/

namespace Falconer
open Set MeasureTheory

theorem sqrt_dimension_le (d : ℕ) : Real.sqrt (d : ℝ) ≤ (d : ℝ)+1 := by
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · nlinarith [sq_nonneg (d : ℝ),Nat.cast_nonneg (α := ℝ) d]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_DescriptorGraph
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual descriptor counts supply the local graph witnesses -/

namespace Falconer
open Set MeasureTheory Metric
open scoped ENNReal
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

theorem parallelGoodSet_local_test (Q : DyadicCube d) (hQ : Q.side = 1)
    (ρ : Measure (Space d)) {a g p : ℕ} (hag : a ≤ g) (hgp : g ≤ p)
    (X P : List (Fin d → Bool)) (hX : X.length = a)
    (w : Sphere d) (W T : ℝ) (hT : 0 ≤ T)
    (hw : w ∈ Regularization.parallelGoodSet Q ρ g p (X++P) W T) :
    DyadicParallelTest (Q.descendant X) ((Q.descendant X).occupiedPaths ρ (p-a))
      (g-a) P w W ⌈T⌉₊ := by
  have hscale : (Q.descendant X).side/(2:ℝ)^(g-a) = 1/(2:ℝ)^g := by
    rw [Q.descendant_side,hX,hQ,div_div,← pow_add,Nat.add_sub_of_le hag]
  let S := ((Q.descendant X).occupiedPaths ρ (p-a)).filter fun z =>
    z.take (g-a) = P.take (g-a) ∧
    ‖((Q.descendant X).descendant z).center-((Q.descendant X).descendant P).center‖ ≤
      Real.sqrt d*((Q.descendant X).side/(2:ℝ)^(g-a)) ∧
    ‖perpendicularPart (w:Space d)
      (((Q.descendant X).descendant z).center-((Q.descendant X).descendant P).center)‖ ≤ W
  have hinj : Function.Injective (fun z : List (Fin d → Bool) => X++z) := by
    intro u v huv
    exact List.append_cancel_left huv
  have hsub : S.image (fun z => X++z) ⊆
      (Regularization.parallelTestCells Q ρ g p (X++P)).filter (fun z =>
        ‖perpendicularPart (w:Space d) ((Q.descendant z).center-(Q.descendant (X++P)).center)‖ ≤ W) := by
    intro z hz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hu,_,hdist,hperp⟩ := Finset.mem_filter.mp hu
    obtain ⟨hu,hocc⟩ := Finset.mem_filter.mp hu
    have hulen := (mem_cubePaths _ _ _).mp hu
    apply Finset.mem_filter.mpr
    constructor
    · simp only [Regularization.parallelTestCells,Regularization.occupiedCenterCells,
        Finset.mem_filter]
      refine ⟨?_,?_,?_⟩
      · apply (mem_cubePaths _ _ _).mpr
        simp only [List.length_append,hX,hulen]
        omega
      · simpa only [Q.descendant_append] using hocc
      · rw [mem_ball,dist_eq_norm,Q.descendant_append,Q.descendant_append]
        apply hdist.trans_lt
        rw [hscale]
        have hs := sqrt_dimension_le d
        have hr : Real.sqrt d < 10*((d:ℝ)+1) := by
          nlinarith [Nat.cast_nonneg (α := ℝ) d]
        simpa only [div_eq_mul_inv,one_mul] using
          mul_lt_mul_of_pos_right hr (by positivity : 0 < 1/(2:ℝ)^g)
    · simpa only [Q.descendant_append] using hperp
  have hcard : S.card ≤ Regularization.parallelTestCount Q ρ g p (X++P) W w := by
    calc
      S.card = (S.image (fun z => X++z)).card :=
        (Finset.card_image_of_injective S hinj).symm
      _ ≤ _ := Finset.card_le_card hsub
  have hcount : (Regularization.parallelTestCount Q ρ g p (X++P) W w : ℝ) ≤ T := by
    unfold Regularization.parallelGoodSet at hw
    split_ifs at hw with hocc
    · simpa only [ENNReal.toReal_natCast,ENNReal.toReal_ofReal hT] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hw
    · exact False.elim hw
  exact hcard.trans ((Nat.cast_le (α := ℝ)).mp (hcount.trans (Nat.le_ceil T)))

theorem descriptorEndpointGood_graph_test (Q : DyadicCube d) (hQ : Q.side = 1)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    {a g p : ℕ} (hag : a ≤ g) (hgp : g ≤ p)
    (X P : List (Fin d → Bool)) (hX : X.length = a) (hP : P.length = p-a)
    {x : Space d} (hx : x ∈ ((Q.descendant X).descendant P).carrier)
    (w : Sphere d)
    (hw : (x,w) ∈ descriptorEndpointGood Q ρ m N σ J i (.parallel g p)) :
    DyadicParallelTest (Q.descendant X) ((Q.descendant X).occupiedPaths ρ (p-a))
      (g-a) P w (angularTestWidth N σ J i p)
      ⌈((2:ℝ)^N)^(PlanarFalconer.height
        (fun n : ℕ => m n-((d:ℝ)/2)*(n:ℝ)/N) g p+1000*((d:ℝ)+1)*σ)⌉₊ := by
  apply parallelGoodSet_local_test Q hQ ρ hag hgp X P hX w _ _ (by positivity)
  apply (descriptorEndpointGood_on_cell Q ρ m N σ J i (.parallel g p) (X++P) ?_
    (by simpa only [Q.descendant_append] using hx) w).mp hw
  simp only [PlanarFalconer.descriptorAnchor,List.length_append,hX,hP]
  omega

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularEnvelopeGraph
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual profile graph estimate on the admissible energy envelope

Restriction to a child is implemented by the existing spatial cell symbol.
The original restricted endpoint integral is unchanged, and the support
condition is propagated explicitly to the child's good set.
-/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap

theorem finiteEnvelopeMaximum_nonneg {ι : Type*} (S : Finset ι) (F : ι → ℝ) :
    0 ≤ finiteEnvelopeMaximum S F :=
  le_csSup ((S.finite_toSet.image F).insert 0).bddAbove (Or.inl rfl)

theorem finiteEnvelopeMaximum_le {ι : Type*} (S : Finset ι) (F : ι → ℝ)
    {H : ℝ} (hH : 0 ≤ H) (h : ∀ i ∈ S, F i ≤ H) :
    finiteEnvelopeMaximum S F ≤ H := by
  change sSup (insert (0:ℝ) (F '' (S : Set ι))) ≤ H
  apply csSup_le (show (insert (0:ℝ) (F '' (S : Set ι))).Nonempty from ⟨0,Or.inl rfl⟩)
  intro x hx
  rcases hx with rfl | ⟨i,hi,rfl⟩
  · exact hH
  · exact h i hi

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_MaskSupport
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Buffered masks retain their good-direction support under differentiation -/

namespace Falconer
open Set MeasureTheory
open scoped Topology

theorem capCutoffAmbient_tsupport_subset {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d)) (U : Set (Sphere d)) :
    tsupport (capCutoffAmbient δ hδ S U) ⊆
      ⋃ c ∈ cutoffCapCenters δ S U, Metric.closedBall (c : Space d) δ := by
  apply closure_minimal _ (isClosed_biUnion_finset (fun _ _ => Metric.isClosed_closedBall))
  intro x hx
  obtain ⟨c,hc,hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  apply mem_iUnion₂.mpr ⟨c,hc,?_⟩
  have hb : capBump δ hδ c x ≠ 0 := (mul_ne_zero_iff.mp hn).1
  have hm : x ∈ Metric.ball (c : Space d) δ := by
    change x ∈ Metric.ball (c : Space d) (capBump δ hδ c).rOut
    rw [← (capBump δ hδ c).support_eq]
    exact hb
  exact Metric.ball_subset_closedBall hm

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorAmbient
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth ambient extensions of the actual spatially anchored masks

At each spatial point there is at most one active anchor cell. Consequently
the ambient derivative bound has no factor counting anchor cells.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)
open scoped ContDiff
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem descriptorAmbientMask_tsupport_good (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (S : Finset (Sphere d)) (x : Space d) (w : Sphere d)
    (hw : (w : Space d) ∈ tsupport (descriptorAmbientMask Q ρ m N σ J i b S x)) :
    (x,w) ∈ descriptorEndpointGood Q ρ m N σ J (i+1) b := by
  intro p hp hx
  have he := funext (descriptorAmbientMask_on_cell Q ρ m N σ J i b S p
    ((mem_cubePaths d _ p).mp hp) hx)
  rw [he] at hw
  have hs := capCutoffAmbient_tsupport_subset (descriptorMaskRadius_pos N σ b) S
    (descriptorGoodDirections Q ρ m N σ J (i+1) p b) hw
  obtain ⟨c,hc,hwc⟩ := Set.mem_iUnion₂.mp hs
  exact (Finset.mem_filter.mp hc).2 w
    (by simpa only [Metric.mem_closedBall,Subtype.dist_eq] using hwc)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ReachedMasks
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing reached masks after passing to positive energy

A reached anchor mask is spatially constant on its descendant cell. It
can therefore be taken outside that endpoint transform. Its bounded
angular factor is removed only from the positive independent energy.
-/

namespace Falconer
open Set MeasureTheory

theorem endpointTransform_angular_factor {d : ℕ} (ρ : Measure (Space d))
    (M : ℝ) (b : Space d → Sphere d → ℂ) (m : Sphere d → ℂ)
    (r : ℝ) (w : Sphere d) :
    endpointTransform ρ M (fun x w => m w * b x w) r w =
      m w * endpointTransform ρ M b r w := by
  unfold endpointTransform
  have he : (fun x => Complex.exp (Complex.I * (r : ℂ) *
      (inner ℝ (w : Space d) x : ℂ)) * (m w * b x w)) =
      fun x => m w * (Complex.exp (Complex.I * (r : ℂ) *
        (inner ℝ (w : Space d) x : ℂ)) * b x w) := by
    funext x
    ring
  rw [he, integral_const_mul, mul_smul_comm]

theorem sphereMoment_factor_le {d : ℕ} (U : ℝ × Sphere d → ℂ)
    (hU : Measurable U) (m : Sphere d → ℂ) (hm : Measurable m)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hmB : ∀ w, ‖m w‖ ≤ B) (hUC : ∀ z, ‖U z‖ ≤ C) (r : ℝ) :
    sphereMoment (fun z => m z.2 * U z) r ≤ B^2 * sphereMoment U r := by
  have hmU : Measurable (fun w => m w * U (r,w)) :=
    hm.mul (hU.comp (measurable_const.prodMk measurable_id))
  have hbound (w : Sphere d) : ‖m w * U (r,w)‖ ≤ B*C := by
    rw [norm_mul]
    exact mul_le_mul (hmB w) (hUC _) (norm_nonneg _) hB
  have hleft := sphere_norm_square_integrable _ hmU (mul_nonneg hB hC) hbound
  have hright := (sphere_norm_square_integrable (fun w => U (r,w))
    (hU.comp (measurable_const.prodMk measurable_id)) hC (fun w => hUC _)).const_mul (B^2)
  change (∫ w, ‖m w * U (r,w)‖^2 ∂sphereMeasure d) ≤
    B^2 * (∫ w, ‖U (r,w)‖^2 ∂sphereMeasure d)
  rw [← integral_const_mul]
  apply integral_mono hleft hright
  intro w
  change ‖m w * U (r,w)‖^2 ≤ B^2 * ‖U (r,w)‖^2
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right
    ((sq_le_sq₀ (norm_nonneg _) hB).mpr (hmB w)) (sq_nonneg _)

/-- Removing two reached angular factors costs only their squared sup
norms. Every unreached spatial mask remains inside its endpoint transform. -/
theorem independentAngularEnergy_remove_factors {d : ℕ} (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (U V : ℝ × Sphere d → ℂ) (hU : Measurable U) (hV : Measurable V)
    (m n : Sphere d → ℂ) (hm : Measurable m) (hn : Measurable n)
    {B C D E : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hmB : ∀ w, ‖m w‖ ≤ B) (hnC : ∀ w, ‖n w‖ ≤ C)
    (hUD : ∀ z, ‖U z‖ ≤ D) (hVE : ∀ z, ‖V z‖ ≤ E) :
    independentAngularEnergy a v Ψ (fun z => m z.2 * U z) (fun z => n z.2 * V z) ≤
      (B^2*C^2) * independentAngularEnergy a v Ψ U V := by
  have hUm : Measurable (fun z : ℝ × Sphere d => m z.2 * U z) :=
    (hm.comp measurable_snd).mul hU
  have hVn : Measurable (fun z : ℝ × Sphere d => n z.2 * V z) :=
    (hn.comp measurable_snd).mul hV
  have hUmB (z : ℝ × Sphere d) : ‖m z.2 * U z‖ ≤ B*D := by
    rw [norm_mul]
    exact mul_le_mul (hmB _) (hUD _) (norm_nonneg _) hB
  have hVnC (z : ℝ × Sphere d) : ‖n z.2 * V z‖ ≤ C*E := by
    rw [norm_mul]
    exact mul_le_mul (hnC _) (hVE _) (norm_nonneg _) hC
  have hi := independentAngularIntegrand_integrable v Ψ _ _ hUm hVn
    (mul_nonneg hB hD) (mul_nonneg hC hE) hUmB hVnC
  have hj := (independentAngularIntegrand_integrable v Ψ U V hU hV hD hE hUD hVE).const_mul
    (B^2*C^2)
  have hpoint (r : ℝ) :
      sphereMoment (fun z => m z.2 * U z) r * sphereMoment (fun z => n z.2 * V z) r ≤
        (B^2*C^2) * (sphereMoment U r * sphereMoment V r) := by
    calc
      _ ≤ (B^2 * sphereMoment U r) * (C^2 * sphereMoment V r) :=
        mul_le_mul (sphereMoment_factor_le U hU m hm hB hD hmB hUD r)
          (sphereMoment_factor_le V hV n hn hC hE hnC hVE r)
          (sphereMoment_nonneg _ _) (mul_nonneg (sq_nonneg _) (sphereMoment_nonneg _ _))
      _ = _ := by ring
  unfold independentAngularEnergy
  calc
    _ ≤ (2 : ℝ)^((d : ℝ)*(v-a)) *
        ∫ r, (B^2*C^2) * (sphereMoment U r * sphereMoment V r)
          ∂PlanarFalconer.sourceAngularShellMeasure v Ψ :=
      mul_le_mul_of_nonneg_left (integral_mono hi hj hpoint) (by positivity)
    _ = _ := by rw [integral_const_mul]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_ReachedMaskJets
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalized mask derivatives at reached anchors

Reached masks agree as ambient functions throughout a child cell. All their
ambient jets therefore agree too. Radius normalization makes each fixed
order uniformly bounded before any scale or descriptor is selected.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)
open scoped ContDiff

theorem descriptorAmbientMask_reached_eq {d : ℕ} (Q : DyadicCube d) (hQ : 0 < Q.side)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PolicyDescriptor) (S : Finset (Sphere d)) (X : List (Fin d → Bool))
    (hb : descriptorAnchor b ≤ X.length) {x : Space d}
    (hx : x ∈ (Q.descendant X).carrier) :
    descriptorAmbientMask Q ρ m N σ J i b S x =
      descriptorAmbientMask Q ρ m N σ J i b S (Q.descendant X).center := by
  let p := X.take (descriptorAnchor b)
  let q := X.drop (descriptorAnchor b)
  have hp : p.length = descriptorAnchor b := by
    simp only [p,List.length_take,Nat.min_eq_left hb]
  have hprefix (y : Space d) (hy : y ∈ (Q.descendant X).carrier) :
      y ∈ (Q.descendant p).carrier := by
    have he : X = p++q := (List.take_append_drop _ _).symm
    rw [he,Q.descendant_append] at hy
    exact (Q.descendant p).descendant_subset q hy
  funext z
  rw [descriptorAmbientMask_on_cell Q ρ m N σ J i b S p hp (hprefix x hx),
    descriptorAmbientMask_on_cell Q ρ m N σ J i b S p hp
      (hprefix _ ((Q.descendant X).center_mem (Q.descendant_side_pos hQ X)))]

theorem normalizedDescriptorJet_reached {d : ℕ} (Q : DyadicCube d) (hQ : 0 < Q.side)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PolicyDescriptor) (S : Finset (Sphere d)) (k : ℕ) (v : Fin k → Space d)
    (X : List (Fin d → Bool)) (hb : descriptorAnchor b ≤ X.length) {x : Space d}
    (hx : x ∈ (Q.descendant X).carrier) (w : Sphere d) :
    normalizedDescriptorJet Q ρ m N σ J i b S k v x w =
      normalizedDescriptorJet Q ρ m N σ J i b S k v (Q.descendant X).center w := by
  unfold normalizedDescriptorJet
  rw [descriptorAmbientMask_reached_eq Q hQ ρ m N σ J i b S X hb hx]


theorem normalizedDescriptorJet_support {d : ℕ} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PolicyDescriptor) (S : Finset (Sphere d)) (k : ℕ) (v : Fin k → Space d)
    (x : Space d) (w : Sphere d)
    (h : normalizedDescriptorJet Q ρ m N σ J i b S k v x w ≠ 0) :
    (x,w) ∈ descriptorEndpointGood Q ρ m N σ J (i+1) b := by
  have hn : iteratedFDeriv ℝ k (descriptorAmbientMask Q ρ m N σ J i b S x)
      (w : Space d) ≠ 0 := by
    intro hz
    apply h
    simp only [normalizedDescriptorJet,hz,zero_apply,mul_zero,
      Complex.ofReal_zero]
  exact descriptorAmbientMask_tsupport_good Q ρ m N σ J i b S x w
    (support_iteratedFDeriv_subset (𝕜 := ℝ) k hn)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_DescriptorJetProduct
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Indexed products of actual normalized descriptor derivatives

The index set distinguishes repeated descriptors. Its total derivative
order controls the norm independently of the number of undifferentiated
masks. Reached factors split off as one angular function on each cell.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)

theorem descriptorJetProduct_reached_split {d : ℕ} {ι : Type*}
    (Q : DyadicCube d) (hQ : 0 < Q.side)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (F : Finset ι) (b : ι → PolicyDescriptor)
    (S : PolicyDescriptor → Finset (Sphere d)) (k : ι → ℕ)
    (v : (j : ι) → Sphere d → Fin (k j) → Space d)
    (X : List (Fin d → Bool)) {x : Space d} (hx : x ∈ (Q.descendant X).carrier)
    (w : Sphere d) :
    descriptorJetProduct Q ρ m N σ J i F b S k v x w =
      descriptorJetProduct Q ρ m N σ J i
        (F.filter (fun j => descriptorAnchor (b j) ≤ X.length)) b S k v (Q.descendant X).center w *
      descriptorJetProduct Q ρ m N σ J i
        (F.filter (fun j => X.length < descriptorAnchor (b j))) b S k v x w := by
  classical
  unfold descriptorJetProduct
  have hsplit := (Finset.prod_filter_mul_prod_filter_not F
    (fun j => descriptorAnchor (b j) ≤ X.length)
    (fun j => normalizedDescriptorJet Q ρ m N σ J i (b j) (S (b j)) (k j) (v j w) x w)).symm
  rw [show F.filter (fun j => ¬descriptorAnchor (b j) ≤ X.length) =
    F.filter (fun j => X.length < descriptorAnchor (b j)) by ext j; simp] at hsplit
  refine hsplit.trans ?_
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  exact normalizedDescriptorJet_reached Q hQ ρ m N σ J i (b j) (S (b j)) (k j)
    (v j w) X (Finset.mem_filter.mp hj).2 hx w

theorem descriptorJetProduct_support {d : ℕ} {ι : Type*}
    (Q : DyadicCube d) (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ)
    (σ : ℝ) (J i : ℕ) (F : Finset ι) (b : ι → PolicyDescriptor)
    (S : PolicyDescriptor → Finset (Sphere d)) (k : ι → ℕ)
    (v : (j : ι) → Sphere d → Fin (k j) → Space d) (x : Space d) (w : Sphere d)
    (h : descriptorJetProduct Q ρ m N σ J i F b S k v x w ≠ 0) :
    ∀ j ∈ F, (x,w) ∈ descriptorEndpointGood Q ρ m N σ J (i+1) (b j) := by
  intro j hj
  apply normalizedDescriptorJet_support Q ρ m N σ J i (b j) (S (b j)) (k j) (v j w) x w
  exact (Finset.prod_ne_zero_iff.mp h) j hj

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_DescriptorJetMeasurable
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurability of the actual anchored mask jets

The spatial variable only selects one of finitely many Borel anchor cells.
Within such a cell all angular jets are derivatives of its fixed smooth mask.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)
open scoped ContDiff
attribute [local instance] Classical.propDecidable

 theorem normalizedDescriptorJet_anchor_sum {d : ℕ} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PolicyDescriptor) (S : Finset (Sphere d)) (k : ℕ)
    (v : Fin k → Space d) (x : Space d) (w : Sphere d) :
    normalizedDescriptorJet Q ρ m N σ J i b S k v x w =
      ∑ p ∈ cubePaths d (descriptorAnchor b),
        if x ∈ (Q.descendant p).carrier then
          (((descriptorMaskRadius N σ b)^k *
            (iteratedFDeriv ℝ k
              (capCutoffAmbient (descriptorMaskRadius N σ b)
                (descriptorMaskRadius_pos N σ b) S
                (descriptorGoodDirections Q ρ m N σ J (i+1) p b)) w) v : ℝ) : ℂ)
        else 0 := by
  classical
  by_cases hx : x ∈ Q.carrier
  · obtain ⟨p,hp,hxp⟩ := Q.mem_descendant_at_depth (descriptorAnchor b) hx
    rw [Finset.sum_eq_single p]
    · have he := funext (descriptorAmbientMask_on_cell Q ρ m N σ J i b S p
        ((mem_cubePaths d _ p).mp hp) hxp)
      simp only [normalizedDescriptorJet,he,ite_eq_left hxp]
    · intro q hq hqp
      have hdis := Q.descendants_disjoint
        (((mem_cubePaths d _ q).mp hq).trans ((mem_cubePaths d _ p).mp hp).symm) hqp
      exact ite_eq_right (fun hq => Set.disjoint_left.mp hdis hq hxp)
    · exact fun hn => (hn hp).elim
  · have hz : normalizedDescriptorJet Q ρ m N σ J i b S k v x w = 0 := by
      simp only [normalizedDescriptorJet,descriptorAmbientMask_off_parent Q ρ m N σ J i b S hx,
        iteratedFDeriv_fun_zero,Pi.zero_apply,zero_apply,mul_zero,Complex.ofReal_zero]
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro p _
    exact ite_eq_right (fun hp => hx (Q.descendant_subset p hp))

 theorem normalizedDescriptorJet_measurable {d : ℕ} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PolicyDescriptor) (S : Finset (Sphere d)) (k : ℕ)
    (v : Sphere d → Fin k → Space d) (hv : Measurable v) :
    Measurable (fun z : Space d × Sphere d =>
      normalizedDescriptorJet Q ρ m N σ J i b S k (v z.2) z.1 z.2) := by
  classical
  simp_rw [normalizedDescriptorJet_anchor_sum]
  apply Finset.measurable_sum
  intro p _
  let f := capCutoffAmbient (descriptorMaskRadius N σ b)
    (descriptorMaskRadius_pos N σ b) S
    (descriptorGoodDirections Q ρ m N σ J (i+1) p b)
  have hf : ContDiff ℝ ∞ f := capCutoffAmbient_contDiff (descriptorMaskRadius_pos N σ b) S _
  have he : Continuous (fun z : Space d × (Fin k → Space d) =>
      (iteratedFDeriv ℝ k f z.1) z.2) :=
    ((hf.continuous_iteratedFDeriv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp continuous_fst).eval continuous_snd
  have hm : Measurable (fun w : Sphere d =>
      (((descriptorMaskRadius N σ b)^k * (iteratedFDeriv ℝ k f w) (v w) : ℝ) : ℂ)) :=
    ((he.measurable.comp (continuous_subtype_val.measurable.prodMk hv)).const_mul _).complex_ofReal
  exact (hm.comp measurable_snd).ite
    ((Q.descendant p).measurable.preimage measurable_fst) measurable_const

 theorem descriptorJetProduct_measurable {d : ℕ} {ι : Type*} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (F : Finset ι) (b : ι → PolicyDescriptor) (S : PolicyDescriptor → Finset (Sphere d))
    (k : ι → ℕ) (v : (j : ι) → Sphere d → Fin (k j) → Space d)
    (hv : ∀ j ∈ F, Measurable (v j)) :
    Measurable (Function.uncurry (descriptorJetProduct Q ρ m N σ J i F b S k v)) := by
  apply Finset.measurable_prod
  intro j hj
  exact normalizedDescriptorJet_measurable Q ρ m N σ J i (b j) (S (b j)) (k j) (v j) (hv j hj)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_DescriptorJetRemoval
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reached differentiated masks in positive independent energy

Every unreached occurrence remains in the endpoint transform. The cost of
removing reached factors depends on the fixed total jet order, not on the
number of undifferentiated masks or the scale.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)

theorem descriptorJetBound_one_le (d K : ℕ) : 1 ≤ descriptorJetBound d K :=
  (normalizedDescriptorJet_order_bound d K).choose_spec.1

theorem descriptorJetProduct_norm_le {d K : ℕ} {ι : Type*} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (F : Finset ι) (b : ι → PolicyDescriptor) (S : PolicyDescriptor → Finset (Sphere d))
    (k : ι → ℕ) (v : (j : ι) → Sphere d → Fin (k j) → Space d)
    (hsep : ∀ j ∈ F, ∀ w ∈ S (b j), ∀ z ∈ S (b j), w ≠ z →
      descriptorMaskRadius N σ (b j)/2 ≤ dist w z)
    (horder : (∑ j ∈ F, k j) ≤ K)
    (hv : ∀ j ∈ F, ∀ w l, ‖v j w l‖ ≤ 1) (x : Space d) (w : Sphere d) :
    ‖descriptorJetProduct Q ρ m N σ J i F b S k v x w‖ ≤ (descriptorJetBound d K)^K := by
  have hA := descriptorJetBound_one_le d K
  have hbound := (normalizedDescriptorJet_order_bound d K).choose_spec.2
  rw [descriptorJetProduct,norm_prod]
  calc
    _ ≤ ∏ j ∈ F, (descriptorJetBound d K)^(k j) := by
      apply Finset.prod_le_prod (fun j _ => norm_nonneg _)
      intro j hj
      exact hbound Q ρ m N σ J i (b j) (S (b j)) (hsep j hj) (k j)
        ((Finset.single_le_sum (fun l _ => Nat.zero_le (k l)) hj).trans horder)
        (v j w) (hv j hj w) x w
    _ = (descriptorJetBound d K)^(∑ j ∈ F, k j) := Finset.prod_pow_eq_pow_sum F k _
    _ ≤ (descriptorJetBound d K)^K := pow_le_pow_right₀ hA horder

/-- Evaluate the spatial parameter before proving angular measurability. -/
theorem descriptorJetProduct_fixed_measurable {d : ℕ} {ι : Type*}
    (Q : DyadicCube d) (ρ : Measure (Space d)) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (F : Finset ι)
    (b : ι → PolicyDescriptor) (S : PolicyDescriptor → Finset (Sphere d))
    (k : ι → ℕ) (v : (j : ι) → Sphere d → Fin (k j) → Space d)
    (hv : ∀ j ∈ F, Measurable (v j)) (x : Space d) :
    Measurable (fun w => descriptorJetProduct Q ρ m N σ J i F b S k v x w) := by
  exact (descriptorJetProduct_measurable Q ρ m N σ J i F b S k v hv).of_uncurry_left

/-- Bounded angular factors can be removed from two finite endpoint laws. -/
theorem independentAngularEnergy_endpoint_remove_factors {d : ℕ}
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P)
    (f g : Space d → Sphere d → ℂ)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hfC : ∀ x w, ‖f x w‖ ≤ C) (hgD : ∀ x w, ‖g x w‖ ≤ D)
    (p q : Sphere d → ℂ) (hp : Measurable p) (hq : Measurable q)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hpA : ∀ w, ‖p w‖ ≤ A) (hqB : ∀ w, ‖q w‖ ≤ B)
    (a t : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure t Ψ)] :
    independentAngularEnergy a t Ψ
      (fun z => p z.2 * endpointTransform μ M f z.1 z.2)
      (fun z => q z.2 * endpointTransform ν P g z.1 z.2) ≤
    A^2*B^2*independentAngularEnergy a t Ψ
      (fun z => endpointTransform μ M f z.1 z.2)
      (fun z => endpointTransform ν P g z.1 z.2) := by
  exact independentAngularEnergy_remove_factors a t Ψ _ _
    (measurable_endpointTransform μ M f hf) (measurable_endpointTransform ν P g hg)
    p q hp hq hA hB
    (div_nonneg (mul_nonneg hC measureReal_nonneg) hM.le)
    (div_nonneg (mul_nonneg hD measureReal_nonneg) hP.le)
    hpA hqB (fun z => endpointTransform_norm_le μ hM f hfC z.1 z.2)
    (fun z => endpointTransform_norm_le ν hP g hgD z.1 z.2)

 theorem endpointTransform_descriptorJetProduct_split {d : ℕ} {ι : Type*}
    (Q : DyadicCube d) (hQ : 0 < Q.side)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (F : Finset ι) (b : ι → PolicyDescriptor) (S : PolicyDescriptor → Finset (Sphere d))
    (k : ι → ℕ) (v : (j : ι) → Sphere d → Fin (k j) → Space d)
    (X : List (Fin d → Bool)) (μ : Measure (Space d)) (M : ℝ)
    (f : Space d → Sphere d → ℂ) (r : ℝ) (w : Sphere d) :
    endpointTransform (μ.restrict (Q.descendant X).carrier) M
      (fun x w => descriptorJetProduct Q ρ m N σ J i F b S k v x w * f x w) r w =
    descriptorJetProduct Q ρ m N σ J i
      (F.filter (fun j => descriptorAnchor (b j) ≤ X.length)) b S k v (Q.descendant X).center w *
    endpointTransform (μ.restrict (Q.descendant X).carrier) M
      (fun x w => descriptorJetProduct Q ρ m N σ J i
        (F.filter (fun j => X.length < descriptorAnchor (b j))) b S k v x w * f x w) r w := by
  classical
  rw [← endpointTransform_angular_factor (μ.restrict (Q.descendant X).carrier) M
    (fun x w => descriptorJetProduct Q ρ m N σ J i
      (F.filter (fun j => X.length < descriptorAnchor (b j))) b S k v x w * f x w)
    (fun w => descriptorJetProduct Q ρ m N σ J i
      (F.filter (fun j => descriptorAnchor (b j) ≤ X.length)) b S k v (Q.descendant X).center w) r w]
  unfold endpointTransform
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (Q.descendant X).measurable] with x hx
  rw [descriptorJetProduct_reached_split Q hQ ρ m N σ J i F b S k v X hx w]
  ring

 theorem independentAngularEnergy_descriptorJets_remove {d K : ℕ} {ι τ : Type*}
    (Q : DyadicCube d) (hQ : 0 < Q.side)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (F : Finset ι) (G : Finset τ) (b : ι → PolicyDescriptor) (c : τ → PolicyDescriptor)
    (S : PolicyDescriptor → Finset (Sphere d)) (k : ι → ℕ) (l : τ → ℕ)
    (v : (j : ι) → Sphere d → Fin (k j) → Space d)
    (u : (j : τ) → Sphere d → Fin (l j) → Space d)
    (hsepF : ∀ j ∈ F, ∀ w ∈ S (b j), ∀ z ∈ S (b j), w ≠ z →
      descriptorMaskRadius N σ (b j)/2 ≤ dist w z)
    (hsepG : ∀ j ∈ G, ∀ w ∈ S (c j), ∀ z ∈ S (c j), w ≠ z →
      descriptorMaskRadius N σ (c j)/2 ≤ dist w z)
    (horderF : (∑ j ∈ F, k j) ≤ K) (horderG : (∑ j ∈ G, l j) ≤ K)
    (hv : ∀ j ∈ F, ∀ w t, ‖v j w t‖ ≤ 1) (hu : ∀ j ∈ G, ∀ w t, ‖u j w t‖ ≤ 1)
    (hvm : ∀ j ∈ F, Measurable (v j)) (hum : ∀ j ∈ G, Measurable (u j))
    (X Y : List (Fin d → Bool)) (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {M₁ M₂ : ℝ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (f g : Space d → Sphere d → ℂ)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hfC : ∀ x w, ‖f x w‖ ≤ C₁) (hgC : ∀ x w, ‖g x w‖ ≤ C₂)
    (a t : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure t Ψ)] :
    independentAngularEnergy a t Ψ
      (fun z => endpointTransform (μ.restrict (Q.descendant X).carrier) M₁
        (fun x w => descriptorJetProduct Q ρ m N σ J i F b S k v x w * f x w) z.1 z.2)
      (fun z => endpointTransform (ν.restrict (Q.descendant Y).carrier) M₂
        (fun x w => descriptorJetProduct Q ρ m N σ J i G c S l u x w * g x w) z.1 z.2) ≤
    ((descriptorJetBound d K)^K)^2 * ((descriptorJetBound d K)^K)^2 *
    independentAngularEnergy a t Ψ
      (fun z => endpointTransform (μ.restrict (Q.descendant X).carrier) M₁
        (fun x w => descriptorJetProduct Q ρ m N σ J i
          (F.filter (fun j => X.length < descriptorAnchor (b j))) b S k v x w * f x w) z.1 z.2)
      (fun z => endpointTransform (ν.restrict (Q.descendant Y).carrier) M₂
        (fun x w => descriptorJetProduct Q ρ m N σ J i
          (G.filter (fun j => Y.length < descriptorAnchor (c j))) c S l u x w * g x w) z.1 z.2) := by
  classical
  simp_rw [endpointTransform_descriptorJetProduct_split Q hQ ρ m N σ J i F b S k v,
    endpointTransform_descriptorJetProduct_split Q hQ ρ m N σ J i G c S l u]
  let A := (descriptorJetBound d K)^K
  have hA : 0 ≤ A := pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le d K)) K
  have hF (H : Finset ι) (hH : H ⊆ F) (x : Space d) (w : Sphere d) :
      ‖descriptorJetProduct Q ρ m N σ J i H b S k v x w‖ ≤ A :=
    descriptorJetProduct_norm_le Q ρ m N σ J i H b S k v
      (fun j hj => hsepF j (hH hj)) ((Finset.sum_le_sum_of_subset hH).trans horderF)
      (fun j hj => hv j (hH hj)) x w
  have hG (H : Finset τ) (hH : H ⊆ G) (x : Space d) (w : Sphere d) :
      ‖descriptorJetProduct Q ρ m N σ J i H c S l u x w‖ ≤ A :=
    descriptorJetProduct_norm_le Q ρ m N σ J i H c S l u
      (fun j hj => hsepG j (hH hj)) ((Finset.sum_le_sum_of_subset hH).trans horderG)
      (fun j hj => hu j (hH hj)) x w
  let FX := F.filter (fun j => X.length < descriptorAnchor (b j))
  let GY := G.filter (fun j => Y.length < descriptorAnchor (c j))
  let RX := F.filter (fun j => descriptorAnchor (b j) ≤ X.length)
  let RY := G.filter (fun j => descriptorAnchor (c j) ≤ Y.length)
  let f' := fun x w => descriptorJetProduct Q ρ m N σ J i FX b S k v x w * f x w
  let g' := fun x w => descriptorJetProduct Q ρ m N σ J i GY c S l u x w * g x w
  have hf' : Measurable (Function.uncurry f') :=
    (descriptorJetProduct_measurable Q ρ m N σ J i FX b S k v
      (fun j hj => hvm j ((Finset.filter_subset _ _) hj))).mul hf
  have hg' : Measurable (Function.uncurry g') :=
    (descriptorJetProduct_measurable Q ρ m N σ J i GY c S l u
      (fun j hj => hum j ((Finset.filter_subset _ _) hj))).mul hg
  have hf'C (x : Space d) (w : Sphere d) : ‖f' x w‖ ≤ A*C₁ := by
    change ‖descriptorJetProduct Q ρ m N σ J i FX b S k v x w * f x w‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul (hF FX (Finset.filter_subset _ _) x w) (hfC x w) (norm_nonneg _) hA
  have hg'C (x : Space d) (w : Sphere d) : ‖g' x w‖ ≤ A*C₂ := by
    change ‖descriptorJetProduct Q ρ m N σ J i GY c S l u x w * g x w‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul (hG GY (Finset.filter_subset _ _) x w) (hgC x w) (norm_nonneg _) hA
  exact independentAngularEnergy_endpoint_remove_factors
    (μ.restrict (Q.descendant X).carrier) (ν.restrict (Q.descendant Y).carrier)
    hM₁ hM₂ f' g' hf' hg' (mul_nonneg hA hC₁) (mul_nonneg hA hC₂) hf'C hg'C
    (fun w => descriptorJetProduct Q ρ m N σ J i RX b S k v (Q.descendant X).center w)
    (fun w => descriptorJetProduct Q ρ m N σ J i RY c S l u (Q.descendant Y).center w)
    (descriptorJetProduct_fixed_measurable Q ρ m N σ J i RX b S k v
      (fun j hj => hvm j ((Finset.filter_subset _ _) hj)) _)
    (descriptorJetProduct_fixed_measurable Q ρ m N σ J i RY c S l u
      (fun j hj => hum j ((Finset.filter_subset _ _) hj)) _)
    hA hA (hF RX (Finset.filter_subset _ _) _) (hG RY (Finset.filter_subset _ _) _) a t Ψ

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetDerivativeBounds
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Derivative bounds for individual ambient mask jets

These estimates retain the order of each differentiated mask. Evaluation
on fixed unit vectors is a contraction, so differentiating a mask jet costs
only the corresponding higher derivative of that same mask.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

private theorem norm_iteratedFDeriv_nested {d : ℕ} (f : Space d → ℝ)
    (k t : ℕ) (z : Space d) :
    ‖iteratedFDeriv ℝ t (iteratedFDeriv ℝ k f) z‖ =
      ‖iteratedFDeriv ℝ (k+t) f z‖ := by
  induction t generalizing k with
  | zero => simp
  | succ t ih =>
    rw [← norm_iteratedFDeriv_fderiv, fderiv_iteratedFDeriv,
      LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,ih]
    rw [show k+1+t = k+(t+1) by omega]

private theorem jetEvaluation_norm_le {d k : ℕ} (v : Fin k → Space d)
    (hv : ∀ j, ‖v j‖ ≤ 1) : ‖jetEvaluation v‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro L
  change ‖L v‖ ≤ 1*‖L‖
  have hp : (∏ j, ‖v j‖) ≤ 1 :=
    Finset.prod_le_one (fun j _ => norm_nonneg (v j)) (fun j _ => hv j)
  simpa only [one_mul] using (L.le_opNorm v).trans
    (mul_le_of_le_one_right (norm_nonneg L) hp)

 theorem norm_iteratedFDeriv_jetValue_le {d : ℕ} (f : Space d → ℝ)
    (hf : ContDiff ℝ ∞ f) (k t : ℕ) (v : Fin k → Space d)
    (hv : ∀ j, ‖v j‖ ≤ 1) (z : Space d) :
    ‖iteratedFDeriv ℝ t (fun y => (iteratedFDeriv ℝ k f y) v) z‖ ≤
      ‖iteratedFDeriv ℝ (k+t) f z‖ := by
  have hfd : ContDiff ℝ ∞ (iteratedFDeriv ℝ k f) :=
    hf.iteratedFDeriv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  change ‖iteratedFDeriv ℝ t (jetEvaluation v ∘ iteratedFDeriv ℝ k f) z‖ ≤ _
  rw [(jetEvaluation v).iteratedFDeriv_comp_left hfd.contDiffAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)]
  calc
    _ ≤ ‖jetEvaluation v‖ * ‖iteratedFDeriv ℝ t (iteratedFDeriv ℝ k f) z‖ :=
      ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ t (iteratedFDeriv ℝ k f) z‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (jetEvaluation_norm_le v hv)
    _ = _ := norm_iteratedFDeriv_nested f k t z

 theorem descriptorJetValue_derivatives (d k t : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : DyadicCube d) (ρ : Measure (Space d))
      (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PlanarFalconer.PolicyDescriptor)
      (S : Finset (Sphere d)),
      (∀ w ∈ S, ∀ z ∈ S, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ (v : Fin k → Space d), (∀ j, ‖v j‖ ≤ 1) →
      ∀ (x z : Space d),
        ‖iteratedFDeriv ℝ t (fun y =>
          (iteratedFDeriv ℝ k (descriptorAmbientMask Q ρ m N σ J i b S x) y) v) z‖ ≤
        C * ((descriptorMaskRadius N σ b)⁻¹)^(k+t) := by
  obtain ⟨C,hC,hbound⟩ := descriptorAmbientMask_global_derivatives d (k+t)
  refine ⟨C,hC,?_⟩
  intro Q ρ m N σ J i b S hsep v hv x z
  exact (norm_iteratedFDeriv_jetValue_le _
    (descriptorAmbientMask_contDiff Q ρ m N σ J i b S x) k t v hv z).trans
    (hbound Q ρ m N σ J i b S hsep x z)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_NormalizedJetDerivatives
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scale-normalized ambient derivatives of a single mask -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

 theorem normalizedAmbientDescriptorJet_sphere {d : ℕ} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PlanarFalconer.PolicyDescriptor) (S : Finset (Sphere d))
    (k : ℕ) (v : Fin k → Space d) (x : Space d) (w : Sphere d) :
    (normalizedAmbientDescriptorJet Q ρ m N σ J i b S k v x w : ℂ) =
      normalizedDescriptorJet Q ρ m N σ J i b S k v x w := rfl

 theorem normalizedAmbientDescriptorJet_contDiff {d : ℕ} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PlanarFalconer.PolicyDescriptor) (S : Finset (Sphere d))
    (k : ℕ) (v : Fin k → Space d) (x : Space d) :
    ContDiff ℝ ∞ (normalizedAmbientDescriptorJet Q ρ m N σ J i b S k v x) := by
  exact contDiff_const.mul
    ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Space d) ℝ v).contDiff.comp
      ((descriptorAmbientMask_contDiff Q ρ m N σ J i b S x).iteratedFDeriv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)))

 theorem normalizedAmbientDescriptorJet_derivatives (d k t : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : DyadicCube d) (ρ : Measure (Space d))
      (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PlanarFalconer.PolicyDescriptor)
      (S : Finset (Sphere d)),
      (∀ w ∈ S, ∀ z ∈ S, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ (v : Fin k → Space d), (∀ j, ‖v j‖ ≤ 1) →
      ∀ (x z : Space d),
        ‖iteratedFDeriv ℝ t (normalizedAmbientDescriptorJet Q ρ m N σ J i b S k v x) z‖ ≤
          C * ((descriptorMaskRadius N σ b)⁻¹)^t := by
  obtain ⟨C,hC,hbound⟩ := descriptorJetValue_derivatives d k t
  refine ⟨C,hC,?_⟩
  intro Q ρ m N σ J i b S hsep v hv x z
  have hr := descriptorMaskRadius_pos N σ b
  have hf : ContDiff ℝ ∞ (fun y =>
      (iteratedFDeriv ℝ k (descriptorAmbientMask Q ρ m N σ J i b S x) y) v) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Space d) ℝ v).contDiff.comp
      ((descriptorAmbientMask_contDiff Q ρ m N σ J i b S x).iteratedFDeriv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  change ‖iteratedFDeriv ℝ t (fun y => (descriptorMaskRadius N σ b)^k •
    (iteratedFDeriv ℝ k (descriptorAmbientMask Q ρ m N σ J i b S x) y) v) z‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (hf.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt,
    norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hr.le k)]
  calc
    _ ≤ (descriptorMaskRadius N σ b)^k * (C*((descriptorMaskRadius N σ b)⁻¹)^(k+t)) :=
      mul_le_mul_of_nonneg_left (hbound Q ρ m N σ J i b S hsep v hv x z) (pow_nonneg hr.le k)
    _ = C*((descriptorMaskRadius N σ b)⁻¹)^t := by
      rw [pow_add]
      calc
        _ = ((descriptorMaskRadius N σ b)*(descriptorMaskRadius N σ b)⁻¹)^k *
            (C*((descriptorMaskRadius N σ b)⁻¹)^t) := by rw [mul_pow]; ring
        _ = _ := by rw [mul_inv_cancel₀ hr.ne',one_pow,one_mul]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_UniformJetBudget
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed derivative budget for each normalized mask jet

One constant is selected before all scales and descriptor lists. Only the
sum of actual derivative orders pays an amplitude cost.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

 theorem normalizedAmbientDescriptorJet_uniform_budget (d K L : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (Q : DyadicCube d) (ρ : Measure (Space d))
      (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PlanarFalconer.PolicyDescriptor)
      (S : Finset (Sphere d)),
      (∀ w ∈ S, ∀ z ∈ S, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ D : ℝ, 1 ≤ D → (descriptorMaskRadius N σ b)⁻¹ ≤ D →
      ∀ k ≤ K, ∀ (v : Fin k → Space d), (∀ j, ‖v j‖ ≤ 1) →
      ∀ t ≤ L, ∀ (x z : Space d),
        ‖iteratedFDeriv ℝ t (normalizedAmbientDescriptorJet Q ρ m N σ J i b S k v x) z‖ ≤
          A^(k+t)*D^t := by
  classical
  choose C hC hbound using fun k t => normalizedAmbientDescriptorJet_derivatives d k t
  let A := 1+∑ p ∈ (Finset.range (K+1)).product (Finset.range (L+1)), C p.1 p.2
  have hA : 1 ≤ A := by
    exact le_add_of_nonneg_right (Finset.sum_nonneg
      (fun p (_ : p ∈ (Finset.range (K+1)).product (Finset.range (L+1))) => hC p.1 p.2))
  have hCA (k t : ℕ) (hk : k ≤ K) (ht : t ≤ L) : C k t ≤ A := by
    have hp : (k,t) ∈ (Finset.range (K+1)).product (Finset.range (L+1)) :=
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩
    have hh := Finset.single_le_sum
      (fun p (_ : p ∈ (Finset.range (K+1)).product (Finset.range (L+1))) => hC p.1 p.2) hp
    exact hh.trans (le_add_of_nonneg_left zero_le_one)
  refine ⟨A,hA,?_⟩
  intro Q ρ m N σ J i b S hsep D hD hscale k hk v hv t ht x z
  by_cases hzero : k+t = 0
  · have hk0 : k = 0 := by omega
    have ht0 : t = 0 := by omega
    subst k
    subst t
    simp only [norm_iteratedFDeriv_zero,normalizedAmbientDescriptorJet,pow_zero,
      iteratedFDeriv_zero_apply,one_mul,zero_add]
    have h := descriptorAmbientMask_global_bounds Q ρ m N σ J i b S x z
    simpa only [Real.norm_eq_abs,abs_of_nonneg h.1] using h.2
  · apply (hbound k t Q ρ m N σ J i b S hsep v hv x z).trans
    exact mul_le_mul ((hCA k t hk ht).trans (le_self_pow₀ hA hzero))
      (pow_le_pow_left₀ (inv_nonneg.mpr (descriptorMaskRadius_pos N σ b).le) hscale t)
      (pow_nonneg (inv_nonneg.mpr (descriptorMaskRadius_pos N σ b).le) t)
      (pow_nonneg (zero_le_one.trans hA) (k+t))


private theorem weighted_jet_product_bound {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq ι]
    (F : Finset ι) (f : ι → E → ℝ) (c : ι → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (L : ℕ) (z : E) (hc : ∀ i ∈ F, 0 ≤ c i)
    (hf : ∀ i ∈ F, ContDiff ℝ ∞ (f i))
    (hb : ∀ i ∈ F, ∀ t ≤ L, ‖iteratedFDeriv ℝ t (f i) z‖ ≤ c i*D^t) :
    ∀ t ≤ L, ‖iteratedFDeriv ℝ t (fun w => ∏ i ∈ F, f i w) z‖ ≤
      (∏ i ∈ F, c i)*((F.card:ℝ)*D)^t := by
  induction F using Finset.induction_on with
  | empty =>
    intro t _
    cases t with
    | zero => simp
    | succ t => simp [iteratedFDeriv_succ_const]
  | @insert i F hi ih =>
    have hcF : ∀ j ∈ F, 0 ≤ c j := fun j hj => hc j (Finset.mem_insert_of_mem hj)
    have hfF : ∀ j ∈ F, ContDiff ℝ ∞ (f j) := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hbF : ∀ j ∈ F, ∀ t ≤ L, ‖iteratedFDeriv ℝ t (f j) z‖ ≤ c j*D^t :=
      fun j hj => hb j (Finset.mem_insert_of_mem hj)
    have hih := ih hcF hfF hbF
    intro t ht
    have hfi := hf i (Finset.mem_insert_self _ _)
    have hff : ContDiff ℝ ∞ (fun w => ∏ j ∈ F, f j w) := contDiff_prod hfF
    simp only [Finset.prod_insert hi,Finset.card_insert_of_notMem hi,Nat.cast_add,Nat.cast_one]
    apply (norm_iteratedFDeriv_mul_le hfi hff z (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (t:ℕ∞ω) ≤ ∞)).trans
    calc
      _ ≤ ∑ q ∈ Finset.range (t+1), (t.choose q:ℝ)*(c i*D^q)*
          ((∏ j ∈ F, c j)*((F.card:ℝ)*D)^(t-q)) := by
        apply Finset.sum_le_sum
        intro q hq
        have hqt : q ≤ t := by have := Finset.mem_range.mp hq; omega
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hb i (Finset.mem_insert_self _ _) q (hqt.trans ht))
            (Nat.cast_nonneg _))
          (hih (t-q) ((Nat.sub_le _ _).trans ht)) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hc i (Finset.mem_insert_self _ _))
            (pow_nonneg hD _)))
      _ = (c i*(∏ j ∈ F, c j)) *
          (∑ q ∈ Finset.range (t+1), (t.choose q:ℝ)*D^q*((F.card:ℝ)*D)^(t-q)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        ring
      _ = (c i*(∏ j ∈ F, c j))*(D+(F.card:ℝ)*D)^t := by
        congr 1
        rw [add_pow]
        apply Finset.sum_congr rfl
        intro q _
        ring
      _ = _ := by congr 2; ring

 theorem normalizedAmbientJetProduct_uniform_budget (d K L : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {ι : Type*} (Q : DyadicCube d) (ρ : Measure (Space d))
      (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (F : Finset ι)
      (b : ι → PlanarFalconer.PolicyDescriptor) (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
      (k : ι → ℕ) (v : (j : ι) → Fin (k j) → Space d),
      (∀ j ∈ F, ∀ w ∈ S (b j), ∀ z ∈ S (b j), w ≠ z → descriptorMaskRadius N σ (b j)/2 ≤ dist w z) →
      (∑ j ∈ F, k j) ≤ K → (∀ j ∈ F, ∀ t, ‖v j t‖ ≤ 1) →
      ∀ D : ℝ, 1 ≤ D → (∀ j ∈ F, (descriptorMaskRadius N σ (b j))⁻¹ ≤ D) →
      ∀ x z t, t ≤ L →
        ‖iteratedFDeriv ℝ t (fun w => ∏ j ∈ F,
          normalizedAmbientDescriptorJet Q ρ m N σ J i (b j) (S (b j)) (k j) (v j) x w) z‖ ≤
        A^K*((F.card:ℝ)*A*D)^t := by
  classical
  obtain ⟨A,hA,hbound⟩ := normalizedAmbientDescriptorJet_uniform_budget d K L
  refine ⟨A,hA,?_⟩
  intro ι Q ρ m N σ J i F b S k v hsep horder hv D hD hscale x z t ht
  have hb : ∀ j ∈ F, ∀ q ≤ L,
      ‖iteratedFDeriv ℝ q
        (normalizedAmbientDescriptorJet Q ρ m N σ J i (b j) (S (b j)) (k j) (v j) x) z‖ ≤
        A^(k j)*(A*D)^q := by
    intro j hj q hq
    have hk : k j ≤ K := (Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) hj).trans horder
    convert hbound Q ρ m N σ J i (b j) (S (b j)) (hsep j hj) D hD (hscale j hj)
      (k j) hk (v j) (hv j hj) q hq x z using 1
    all_goals try with_reducible_and_instances rfl
    rw [pow_add,mul_pow]
    ring
  have h := weighted_jet_product_bound F
    (fun j => normalizedAmbientDescriptorJet Q ρ m N σ J i (b j) (S (b j)) (k j) (v j) x)
    (fun j => A^(k j)) (mul_nonneg (zero_le_one.trans hA) (zero_le_one.trans hD)) L z
    (fun j _ => pow_nonneg (zero_le_one.trans hA) _)
    (fun j _ => normalizedAmbientDescriptorJet_contDiff Q ρ m N σ J i (b j) (S (b j)) (k j) (v j) x)
    hb t ht
  rw [Finset.prod_pow_eq_pow_sum] at h
  apply h.trans
  have hAK := pow_le_pow_right₀ hA horder
  calc
    _ = A^(∑ j ∈ F, k j)*((F.card:ℝ)*A*D)^t := by rw [mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right hAK (pow_nonneg (by positivity) _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetChartControl
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rotated chart control for the actual finite products of mask jets

The total derivative order pays the amplitude cost. The number of mask
occurrences enters the derivative scale, and no occurrence is discarded.
All constants are selected before the scale, descriptors, and index type.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

 theorem descriptorJetProduct_chartControl (n K L : ℕ) :
    ∃ A C : ℝ, 1 ≤ A ∧ 1 ≤ C ∧
      ∀ {ι : Type*} (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2)))
        (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (F : Finset ι)
        (b : ι → PlanarFalconer.PolicyDescriptor)
        (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere (n+2)))
        (k : ι → ℕ) (v : (j : ι) → Fin (k j) → Space (n+2)),
      (∀ j ∈ F, ∀ w ∈ S (b j), ∀ z ∈ S (b j), w ≠ z →
        descriptorMaskRadius N σ (b j)/2 ≤ dist w z) →
      (∑ j ∈ F, k j) ≤ K → (∀ j ∈ F, ∀ t, ‖v j t‖ ≤ 1) →
      ∀ D E : ℝ, 1 ≤ D → 1 ≤ E →
      (∀ j ∈ F, (descriptorMaskRadius N σ (b j))⁻¹ ≤ D) →
      (F.card:ℝ)*A*D ≤ E →
      ChartSymbolControl L
        (descriptorJetProduct Q ρ m N σ J i F b S k (fun j _ => v j)) (C*A^K) E := by
  classical
  obtain ⟨A,hA,hAb⟩ := normalizedAmbientJetProduct_uniform_budget (n+2) K L
  obtain ⟨H,hH,hHb⟩ := ambient_symbol_rotated_chart_budget n L
  refine ⟨A,H+1,hA,by linarith,?_⟩
  intro ι Q ρ m N σ J i F b S k v hsep horder hv D E hD hE hscale hDE
  let B : Space (n+2) → Space (n+2) → ℝ := fun x z =>
    ∏ j ∈ F, normalizedAmbientDescriptorJet Q ρ m N σ J i (b j) (S (b j)) (k j) (v j) x z
  let Z : Space (n+2) → Space (n+2) → ℂ := fun x z => (B x z : ℂ)
  have hB (x : Space (n+2)) : ContDiff ℝ ∞ (B x) :=
    contDiff_prod (fun j _ => normalizedAmbientDescriptorJet_contDiff
      Q ρ m N σ J i (b j) (S (b j)) (k j) (v j) x)
  have hZ (x : Space (n+2)) : ContDiff ℝ ∞ (Z x) :=
    Complex.ofRealCLM.contDiff.comp (hB x)
  have he : descriptorJetProduct Q ρ m N σ J i F b S k (fun j _ => v j) =
      fun x (w : Sphere (n+2)) => Z x w := by
    funext x w
    simp only [descriptorJetProduct,Z,B,Complex.ofReal_prod,normalizedAmbientDescriptorJet_sphere]
  have hm := descriptorJetProduct_measurable Q ρ m N σ J i F b S k
    (fun j _ => v j) (fun _ _ => measurable_const)
  rw [he] at hm ⊢
  have hAK : 0 ≤ A^K := pow_nonneg (zero_le_one.trans hA) _
  have hjet (x : Space (n+2)) (t : ℕ) (ht : t ≤ L) (w : Sphere (n+2)) :
      ‖iteratedFDeriv ℝ t (Z x) w‖ ≤ A^K*E^t := by
    have hn := Complex.ofRealLI.norm_iteratedFDeriv_comp_left
      ((hB x).contDiffAt (x := (w : Space (n+2)))) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (t : ℕ∞ω) ≤ ∞)
    change ‖iteratedFDeriv ℝ t (Complex.ofRealLI ∘ B x) w‖ ≤ _
    rw [hn]
    exact (hAb Q ρ m N σ J i F b S k v hsep horder hv D hD hscale x w t ht).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hDE t) hAK)
  refine ⟨hm,?_,?_,?_⟩
  · intro x w
    have h := hjet x 0 (Nat.zero_le _) w
    simp only [norm_iteratedFDeriv_zero,pow_zero,mul_one] at h
    exact h.trans (le_mul_of_one_le_left hAK (by linarith))
  · intro x e y
    exact (hZ x).comp (rotatedChartCurve_contDiff e y)
  · intro e t ht x y hy u hu
    have h := hHb (Z x) (hZ x) (A^K) E hAK hE (hjet x) e y hy u hu t ht
    exact h.trans (by
      have := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (show H ≤ H+1 by linarith) hAK)
        (pow_nonneg (zero_le_one.trans hE) t)
      simpa only [mul_assoc] using this)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetAdmissible
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual differentiated descriptor products as angular symbols

Multiplication by the smooth coefficient of an inverse term preserves
every descriptor support. The derivative scales add under multiplication;
normalization records its exact amplitude cost.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

private theorem iteratedDeriv_product_bound (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {B C D E : ℝ} (hB : 0 ≤ B) (_hC : 0 ≤ C) (hD : 0 ≤ D) (_hE : 0 ≤ E)
    (t : ℕ) (x : ℝ)
    (hb : ∀ j ≤ t, ‖iteratedDeriv j f x‖ ≤ B*D^j)
    (hc : ∀ j ≤ t, ‖iteratedDeriv j g x‖ ≤ C*E^j) :
    ‖iteratedDeriv t (fun x => f x*g x) x‖ ≤ (B*C)*(D+E)^t := by
  have h := norm_iteratedFDeriv_mul_le hf hg x (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (t : ℕ∞ω) ≤ ∞)
  simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h
  apply h.trans
  calc
    _ ≤ ∑ j ∈ Finset.range (t+1), (t.choose j:ℝ)*(B*D^j)*(C*E^(t-j)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjt : j ≤ t := by have := Finset.mem_range.mp hj; omega
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hb j hjt) (Nat.cast_nonneg _))
        (hc (t-j) (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hB (pow_nonneg hD _)))
    _ = (B*C)*(∑ j ∈ Finset.range (t+1), (t.choose j:ℝ)*D^j*E^(t-j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (B*C)*(D+E)^t := by
      congr 1
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro j _
      ring

 theorem ChartSymbolControl.mul {n L : ℕ}
    {b c : Space (n+2) → Sphere (n+2) → ℂ} {B C D E : ℝ}
    (hb : ChartSymbolControl L b B D) (hc : ChartSymbolControl L c C E)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    ChartSymbolControl L (fun x w => b x w*c x w) (B*C) (D+E) := by
  refine ⟨hb.measurable.mul hc.measurable,?_,?_,?_⟩
  · intro x w
    rw [norm_mul]
    exact mul_le_mul (hb.bound x w) (hc.bound x w) (norm_nonneg _) hB
  · intro x e y
    exact (hb.smooth x e y).mul (hc.smooth x e y)
  · intro e t ht x y hy u hu
    exact iteratedDeriv_product_bound _ _ (hb.smooth x e y) (hc.smooth x e y)
      hB hC hD hE t u (fun j hj => hb.derivative e j (hj.trans ht) x y hy u hu)
      (fun j hj => hc.derivative e j (hj.trans ht) x y hy u hu)

 theorem descriptorJetProduct_mul_admissible {n L : ℕ} {ι : Type*}
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (F : Finset ι)
    (b : ι → PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere (n+2)))
    (k : ι → ℕ) (v : (j : ι) → Sphere (n+2) → Fin (k j) → Space (n+2))
    (q : Sphere (n+2) → ℂ) {P C D E : ℝ}
    (hP : 0 < P) (hC : 0 < C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hp : ChartSymbolControl L (descriptorJetProduct Q ρ m N σ J i F b S k v) P D)
    (hq : ChartSymbolControl L (fun _ w => q w) C E) :
    AngularAdmissible L (E+D)
      {z | ∀ j ∈ F, z ∈ descriptorEndpointGood Q ρ m N σ J (i+1) (b j)}
      (normalizedEndpoint (C*P)
        (fun x w => q w*descriptorJetProduct Q ρ m N σ J i F b S k v x w)) := by
  refine ⟨(hq.mul hp hC.le hP.le hE hD).normalized
    (mul_pos hC hP) le_rfl (add_nonneg hE hD),?_⟩
  intro x w hw
  have h := normalizedEndpoint_ne_zero (C*P) _ x w hw
  exact descriptorJetProduct_support Q ρ m N σ J i F b S k v x w (mul_ne_zero_iff.mp h).2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_FactorizedAngularState
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The factorized symbols used by recursive angular states

The descriptor list is part of the type: every descriptor occurs once,
with an explicitly recorded jet. Passing to a deeper cell filters that
list and keeps the same spatial and smooth angular multipliers.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor descriptorAnchor)

namespace DescriptorJetSymbol
variable {n K L : ℕ} {F : Finset PolicyDescriptor} {D : ℝ}

 theorem multiplier_measurable (f : DescriptorJetSymbol n K L F D) (A : ℝ) :
    Measurable (Function.uncurry (f.multiplier A)) :=
  (f.spatial_measurable.comp measurable_fst).mul measurable_const |>.mul
    f.angular_control.measurable

 theorem multiplier_bound (f : DescriptorJetSymbol n K L F D) {A : ℝ} (hA : 0 < A)
    (x : Space (n+2)) (w : Sphere (n+2)) : ‖f.multiplier A x w‖ ≤ A⁻¹ := by
  rw [multiplier,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hA.le)]
  calc
    _ ≤ (1*A⁻¹)*1 := mul_le_mul
      (mul_le_mul_of_nonneg_right (f.spatial_bound x) (inv_nonneg.mpr hA.le))
      (f.angular_control.bound x w) (norm_nonneg _) (by positivity)
    _ = _ := by ring

 theorem value_norm_le (f : DescriptorJetSymbol n K L F D)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hsep : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z →
      descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (x : Space (n+2)) (w : Sphere (n+2)) :
    ‖f.value Q ρ m N σ J i S A x w‖ ≤ ((descriptorJetBound (n+2) K)^K)*A⁻¹ := by
  rw [value,norm_mul]
  exact mul_le_mul
    (descriptorJetProduct_norm_le Q ρ m N σ J i F id S
      (fun b => (f.jet b).order) (fun b _ => (f.jet b).vectors)
      hsep f.order_le (fun b _ _ => (f.jet b).norm_vectors) x w)
    (f.multiplier_bound hA x w) (norm_nonneg _)
    (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _)

 theorem value_admissible (f : DescriptorJetSymbol n K L F D)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ)
    (S : PolicyDescriptor → Finset (Sphere (n+2))) {A E : ℝ}
    (hA : 0 < A) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hjet : ChartSymbolControl L
      (descriptorJetProduct Q ρ m N σ J i F id S
        (fun b => (f.jet b).order) (fun b _ => (f.jet b).vectors)) A E) :
    AngularAdmissible L (D+E)
      {z | ∀ b ∈ F, z ∈ descriptorEndpointGood Q ρ m N σ J (i+1) b}
      (f.value Q ρ m N σ J i S A) := by
  have h := (descriptorJetProduct_mul_admissible Q ρ m N σ J i F id S
    (fun b => (f.jet b).order) (fun b _ => (f.jet b).vectors) (fun w => f.angular w)
    hA (by norm_num) hE hD hjet f.angular_control).spatialMultiplier
      f.spatial f.spatial_measurable f.spatial_bound
  have he : f.value Q ρ m N σ J i S A = fun x w => f.spatial x*
      normalizedEndpoint A (fun x w => f.angular w*
        descriptorJetProduct Q ρ m N σ J i F id S
          (fun b => (f.jet b).order) (fun b _ => (f.jet b).vectors) x w) x w := by
    funext x w
    simp only [value,multiplier,normalizedEndpoint]
    ring
  rw [he]
  simpa only [one_mul,id_eq] using h

 theorem energy_remove_reached (f g : DescriptorJetSymbol n K L F D)
    (Q : DyadicCube (n+2)) (hQ : 0 < Q.side)
    (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hsep : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z →
      descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (X Y : List (Fin (n+2) → Bool))
    (μ ν : Measure (Space (n+2))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (a t : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure t Ψ)] :
    independentAngularEnergy a t Ψ
      (fun z => endpointTransform (μ.restrict (Q.descendant X).carrier) M
        (f.value Q ρ m N σ J i S A) z.1 z.2)
      (fun z => endpointTransform (ν.restrict (Q.descendant Y).carrier) P
        (g.value Q ρ m N σ J i S A) z.1 z.2) ≤
    ((descriptorJetBound (n+2) K)^K)^2 * ((descriptorJetBound (n+2) K)^K)^2 *
    independentAngularEnergy a t Ψ
      (fun z => endpointTransform (μ.restrict (Q.descendant X).carrier) M
        ((f.restrict (F.filter (fun b => X.length < descriptorAnchor b))
          (Finset.filter_subset _ _)).value Q ρ m N σ J i S A) z.1 z.2)
      (fun z => endpointTransform (ν.restrict (Q.descendant Y).carrier) P
        ((g.restrict (F.filter (fun b => Y.length < descriptorAnchor b))
          (Finset.filter_subset _ _)).value Q ρ m N σ J i S A) z.1 z.2) := by
  exact independentAngularEnergy_descriptorJets_remove Q hQ ρ m N σ J i F F id id S
    (fun b => (f.jet b).order) (fun b => (g.jet b).order)
    (fun b _ => (f.jet b).vectors) (fun b _ => (g.jet b).vectors)
    hsep hsep f.order_le g.order_le
    (fun b _ _ => (f.jet b).norm_vectors) (fun b _ _ => (g.jet b).norm_vectors)
    (fun _ _ => measurable_const) (fun _ _ => measurable_const)
    X Y μ ν hM hP (f.multiplier A) (g.multiplier A)
    (f.multiplier_measurable A) (g.multiplier_measurable A)
    (inv_nonneg.mpr hA.le) (inv_nonneg.mpr hA.le)
    (f.multiplier_bound hA) (g.multiplier_bound hA) a t Ψ

end DescriptorJetSymbol
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_InheritedPolicyState
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

 theorem remainingPolicyDescriptors_drop (A : ℕ → ℝ) (N q a₀ t₀ : ℕ) {a p : ℕ} (hap : a ≤ p) :
    (remainingPolicyDescriptors A N q a₀ t₀ a).filter (fun d => p < descriptorAnchor d) =
      remainingPolicyDescriptors A N q a₀ t₀ p := by
  ext d
  simp only [remainingPolicyDescriptors,Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · exact fun h => ⟨⟨h.1,hap.trans_lt h.2⟩,h.2⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorEnvelope
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual descriptor tests used by the angular envelope

These are finite intersections of the original endpoint tests. Passing to
retained lists only weakens these support conditions. No deletion of an
angular factor or analytic estimate is inferred from this set inclusion.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor policyDescriptorList remainingPolicyDescriptors)

variable {d : ℕ}

/-- This uses the continuous profile at the actual normalized integer depths. -/
theorem descriptorListGood_parallel_test (Q : DyadicCube d) (hQ : Q.side = 1)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PolicyDescriptor) {a g p : ℕ} (hag : a ≤ g) (hgp : g ≤ p)
    (hB : PolicyDescriptor.parallel g p ∈ B)
    (X P : List (Fin d → Bool)) (hX : X.length = a) (hP : P.length = p-a)
    {x : Space d} (hx : x ∈ ((Q.descendant X).descendant P).carrier)
    (w : Sphere d)
    (hw : (x,w) ∈ descriptorListGood Q ρ (fun t => m (t/N)) N σ J i B) :
    DyadicParallelTest (Q.descendant X) ((Q.descendant X).occupiedPaths ρ (p-a))
      (g-a) P w (angularTestWidth N σ J i p)
      ⌈((2:ℝ)^N)^(PlanarFalconer.height
        (fun j : ℕ => m ((j:ℝ)/N)-((d:ℝ)/2)*(j:ℝ)/N) g p+
          1000*((d:ℝ)+1)*σ)⌉₊ :=
  descriptorEndpointGood_graph_test Q hQ ρ (fun t => m (t/N)) N σ J i
    hag hgp X P hX hP hx w (hw _ hB)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_NonstationaryPower
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A finite derivative order pays for all graph summations

The polynomial cost of the spatial labels, cap pairs and model masses is
included in `outer`. The derivative order is chosen before `R` or any
cell, cap or endpoint symbol. Constants may depend on that fixed order.
-/

namespace Falconer

theorem positive_power_gain_order {γ : ℝ} (hγ : 0 < γ) (outer T : ℝ) :
    ∃ m : ℕ, ∀ {R K q : ℝ}, 1 ≤ R → 0 ≤ K → 0 ≤ q →
      q ≤ K*R^(-γ) → R^outer*q^m ≤ K^m*R^(-T) := by
  obtain ⟨m,hm⟩ := exists_nat_ge ((T+outer)/γ)
  have horder : T+outer ≤ γ*(m : ℝ) := by
    have h := (div_le_iff₀ hγ).mp hm
    nlinarith
  refine ⟨m,?_⟩
  intro R K q hR hK hq hbound
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  calc
    R^outer*q^m ≤ R^outer*(K*R^(-γ))^m :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq hbound m) (by positivity)
    _ = K^m*R^(outer-γ*(m : ℝ)) := by
      rw [mul_pow,← Real.rpow_mul_natCast hR0.le,← mul_assoc,mul_comm (R^outer),mul_assoc,
        ← Real.rpow_add hR0]
      congr 2
      ring
    _ ≤ K^m*R^(-T) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hR (by linarith)) (pow_nonneg hK m)

/-- The graph order can also cover the derivative budget required by the far step. -/
theorem positive_power_gain_order_ge {γ : ℝ} (hγ : 0 < γ) (outer T : ℝ)
    (minOrder : ℕ) :
    ∃ m : ℕ, minOrder ≤ m ∧ ∀ {R K q : ℝ}, 1 ≤ R → 0 ≤ K → 0 ≤ q →
      q ≤ K*R^(-γ) → R^outer*q^m ≤ K^m*R^(-T) := by
  obtain ⟨m,hm⟩ := positive_power_gain_order hγ outer T
  refine ⟨m+minOrder,by omega,?_⟩
  intro R K q hR hK hq hbound
  have hdecay : R^(-γ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hR (by linarith)
  have hqK : q ≤ K := hbound.trans (mul_le_of_le_one_right hK hdecay)
  calc
    _ = (R^outer*q^m)*q^minOrder := by rw [pow_add]; ring
    _ ≤ (K^m*R^(-T))*K^minOrder :=
      mul_le_mul (hm hR hK hq hbound) (pow_le_pow_left₀ hq hqK _)
        (by positivity) (by positivity)
    _ = _ := by rw [pow_add]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateEnvelope
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Supremum of the factorized recursive angular states

The supremum varies the actual finite jets and the bounded smooth/spatial
multipliers. The displayed descriptor lists and all normalization data stay
fixed. Reached deletion maps each such symbol into the exact shorter list.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)

theorem jetStateBound_nonneg {n : ℕ} (K : ℕ) (A : ℝ)
    (μ ν : Measure (Space (n+2))) (M P a v : ℝ) (Ψ : ℝ → ℝ) :
    0 ≤ jetStateBound K A μ ν M P a v Ψ := by
  unfold jetStateBound
  positivity

 theorem jetStateEnergy_bound {n K L : ℕ} {D : ℝ} {F G : Finset PolicyDescriptor}
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (μ ν : Measure (Space (n+2)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {M P : ℝ} (hM : 0 < M) (hP : 0 < P)
    (a v : ℝ) (Ψ : ℝ → ℝ) [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (f : DescriptorJetSymbol n K L F D) (g : DescriptorJetSymbol n K L G D) :
    jetStateEnergy Q ρ m N σ J i S A μ ν M P a v Ψ f g ≤
      jetStateBound K A μ ν M P a v Ψ := by
  have hbase : 0 ≤ descriptorJetBound (n+2) K :=
    zero_le_one.trans (descriptorJetBound_one_le _ _)
  unfold jetStateBound
  apply independentAngularEnergy_bound a v Ψ
  · positivity
  · positivity
  · intro z
    exact endpointTransform_norm_le μ hM _ (f.value_norm_le Q ρ m N σ J i S hF hA) z.1 z.2
  · intro z
    exact endpointTransform_norm_le ν hP _ (g.value_norm_le Q ρ m N σ J i S hG hA) z.1 z.2

 theorem jetStateValues_bddAbove {n K L : ℕ} {D : ℝ} {F G : Finset PolicyDescriptor}
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (μ ν : Measure (Space (n+2)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {M P : ℝ} (hM : 0 < M) (hP : 0 < P)
    (a v : ℝ) (Ψ : ℝ → ℝ) [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)] :
    BddAbove (jetStateValues n K L D F G Q ρ m N σ J i S A μ ν M P a v Ψ) := by
  refine ⟨jetStateBound K A μ ν M P a v Ψ,?_⟩
  intro h hh
  rcases hh with rfl | ⟨f,g,rfl⟩
  · exact jetStateBound_nonneg K A μ ν M P a v Ψ
  · exact jetStateEnergy_bound Q ρ m N σ J i S hF hG hA μ ν hM hP a v Ψ f g

 theorem jetStateEnergy_le_envelope {n K L : ℕ} {D : ℝ} {F G : Finset PolicyDescriptor}
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (μ ν : Measure (Space (n+2)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {M P : ℝ} (hM : 0 < M) (hP : 0 < P)
    (a v : ℝ) (Ψ : ℝ → ℝ) [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (f : DescriptorJetSymbol n K L F D) (g : DescriptorJetSymbol n K L G D) :
    jetStateEnergy Q ρ m N σ J i S A μ ν M P a v Ψ f g ≤
      jetStateEnvelope n K L D F G Q ρ m N σ J i S A μ ν M P a v Ψ :=
  le_csSup (jetStateValues_bddAbove Q ρ m N σ J i S hF hG hA μ ν hM hP a v Ψ)
    (Or.inr ⟨f,g,rfl⟩)

 theorem jetStateEnvelope_remove_reached {n K L : ℕ} {D : ℝ} (F : Finset PolicyDescriptor)
    (Q : DyadicCube (n+2)) (hQ : 0 < Q.side) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (X Y : List (Fin (n+2) → Bool))
    (μ ν : Measure (Space (n+2))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)] :
    jetStateEnvelope n K L D F F Q ρ m N σ J i S A
      (μ.restrict (Q.descendant X).carrier) (ν.restrict (Q.descendant Y).carrier) M P a v Ψ ≤
    ((descriptorJetBound (n+2) K)^K)^2 * ((descriptorJetBound (n+2) K)^K)^2 *
      jetStateEnvelope n K L D
        (F.filter (fun b => X.length < descriptorAnchor b))
        (F.filter (fun b => Y.length < descriptorAnchor b))
        Q ρ m N σ J i S A
        (μ.restrict (Q.descendant X).carrier) (ν.restrict (Q.descendant Y).carrier) M P a v Ψ := by
  have hFX : ∀ b ∈ F.filter (fun b => X.length < descriptorAnchor b),
      ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z :=
    fun b hb => hF b (Finset.mem_filter.mp hb).1
  have hFY : ∀ b ∈ F.filter (fun b => Y.length < descriptorAnchor b),
      ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z :=
    fun b hb => hF b (Finset.mem_filter.mp hb).1
  apply csSup_le (show (jetStateValues n K L D F F Q ρ m N σ J i S A
    (μ.restrict (Q.descendant X).carrier) (ν.restrict (Q.descendant Y).carrier) M P a v Ψ).Nonempty
    from ⟨0,Or.inl rfl⟩)
  intro h hh
  rcases hh with rfl | ⟨f,g,rfl⟩
  · have hzero : 0 ≤ jetStateEnvelope n K L D _ _ Q ρ m N σ J i S A
        (μ.restrict (Q.descendant X).carrier) (ν.restrict (Q.descendant Y).carrier) M P a v Ψ :=
      le_csSup (jetStateValues_bddAbove Q ρ m N σ J i S hFX hFY hA _ _ hM hP a v Ψ)
        (Or.inl rfl)
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hzero
  · exact (f.energy_remove_reached g Q hQ ρ m N σ J i S hF hA X Y μ ν hM hP a v Ψ).trans
      (mul_le_mul_of_nonneg_left
        (jetStateEnergy_le_envelope Q ρ m N σ J i S hFX hFY hA _ _ hM hP a v Ψ _ _)
        (mul_nonneg (sq_nonneg _) (sq_nonneg _)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateChildren
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual graph children in the factorized angular envelope -/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable
open PlanarFalconer (PolicyDescriptor descriptorAnchor)

 theorem childJetStateMaximum_nonneg (n K L : ℕ) (D : ℝ) (F : Finset PolicyDescriptor)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (X Y : List (Fin (n+2) → Bool)) (j : ℕ) (M a v : ℝ) (Ψ : ℝ → ℝ) :
    0 ≤ childJetStateMaximum n K L D F Q ρ m N σ J i S A X Y j M a v Ψ :=
  finiteEnvelopeMaximum_nonneg _ _

 theorem childJetStateEnvelope_le {n K L : ℕ} (D : ℝ) (F : Finset PolicyDescriptor)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (X Y : List (Fin (n+2) → Bool)) (j : ℕ) (M a v : ℝ) (Ψ : ℝ → ℝ)
    (row : List (Fin (n+2) → Bool) × List (Fin (n+2) → Bool))
    (hrow : row ∈ (Q.descendant X).occupiedPaths ρ j ×ˢ (Q.descendant Y).occupiedPaths ρ j) :
    jetStateEnvelope n K L D F F Q ρ m N σ J i S A
      (ρ.restrict ((Q.descendant X).descendant row.1).carrier)
      (ρ.restrict ((Q.descendant Y).descendant row.2).carrier) M M a v Ψ ≤
    childJetStateMaximum n K L D F Q ρ m N σ J i S A X Y j M a v Ψ := by
  let V : (List (Fin (n+2) → Bool) × List (Fin (n+2) → Bool)) → ℝ := fun c =>
    jetStateEnvelope n K L D F F Q ρ m N σ J i S A
      (ρ.restrict ((Q.descendant X).descendant c.1).carrier)
      (ρ.restrict ((Q.descendant Y).descendant c.2).carrier) M M a v Ψ
  let T := (Q.descendant X).occupiedPaths ρ j ×ˢ (Q.descendant Y).occupiedPaths ρ j
  change V row ≤ sSup (insert 0 (V '' (T : Set _)))
  apply le_csSup ((T.finite_toSet.image V).insert 0).bddAbove
  exact Or.inr ⟨row,hrow,rfl⟩

 theorem childJetStateEnergy_le {n K L : ℕ} {D : ℝ} {F : Finset PolicyDescriptor}
    (Q : DyadicCube (n+2)) (hQ : 0 < Q.side)
    (ρ : Measure (Space (n+2))) [IsFiniteMeasure ρ] (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) {a p : ℕ} (hap : a ≤ p)
    (X Y : List (Fin (n+2) → Bool)) (hX : X.length = a) (hY : Y.length = a)
    (row : List (Fin (n+2) → Bool) × List (Fin (n+2) → Bool))
    (hrow : row ∈ (Q.descendant X).occupiedPaths ρ (p-a) ×ˢ
      (Q.descendant Y).occupiedPaths ρ (p-a))
    {M : ℝ} (hM : 0 < M) (v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (f g : DescriptorJetSymbol n K L F D) :
    jetStateEnergy Q ρ m N σ J i S A
      (ρ.restrict ((Q.descendant X).descendant row.1).carrier)
      (ρ.restrict ((Q.descendant Y).descendant row.2).carrier) M M p v Ψ f g ≤
    ((descriptorJetBound (n+2) K)^K)^2 * ((descriptorJetBound (n+2) K)^K)^2 *
      childJetStateMaximum n K L D (F.filter (fun b => p < descriptorAnchor b))
        Q ρ m N σ J i S A X Y (p-a) M p v Ψ := by
  have hx := Finset.mem_product.mp hrow
  have hxlen : (X++row.1).length = p := by
    rw [List.length_append,hX,(mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hx.1).1]
    omega
  have hylen : (Y++row.2).length = p := by
    rw [List.length_append,hY,(mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hx.2).1]
    omega
  have hstart := jetStateEnergy_le_envelope Q ρ m N σ J i S hF hF hA
    (ρ.restrict ((Q.descendant X).descendant row.1).carrier)
    (ρ.restrict ((Q.descendant Y).descendant row.2).carrier) hM hM p v Ψ f g
  have hremove := jetStateEnvelope_remove_reached (K := K) (L := L) (D := D) F Q hQ ρ m N σ J i S hF hA
    (X++row.1) (Y++row.2) ρ ρ hM hM p v Ψ
  simp only [Q.descendant_append,hxlen,hylen] at hremove
  apply (hstart.trans hremove).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  exact childJetStateEnvelope_le D (F.filter (fun b => p < descriptorAnchor b))
    Q ρ m N σ J i S A X Y (p-a) M p v Ψ row hrow

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateBudget
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform graph budget for factorized angular symbols

The constants are fixed before the descriptor list and scale. Every symbol
in the recursive class then has the same size-one graph control, provided
its explicit mask derivative scale fits inside the displayed graph scale.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

 theorem exists_descriptorJetSymbol_admissible (n K L : ℕ) :
    ∃ B A : ℝ, 1 ≤ B ∧ 1 ≤ A ∧
      ∀ (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
        (N : ℕ) (σ : ℝ) (J i : ℕ) (F : Finset PolicyDescriptor)
        (S : PolicyDescriptor → Finset (Sphere (n+2))),
      (∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ D E H : ℝ, 0 ≤ D → 1 ≤ E → 1 ≤ H →
      (∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ E) → (F.card:ℝ)*B*E ≤ H →
      ∀ f : DescriptorJetSymbol n K L F D,
        AngularAdmissible L (D+H)
          {z | ∀ b ∈ F, z ∈ descriptorEndpointGood Q ρ m N σ J (i+1) b}
          (f.value Q ρ m N σ J i S A) := by
  obtain ⟨B,C,hB,hC,hcontrol⟩ := descriptorJetProduct_chartControl n K L
  have hA : 1 ≤ C*B^K := by
    calc
      1 = (1:ℝ)*1 := by ring
      _ ≤ C*B^K := mul_le_mul hC (one_le_pow₀ hB) (by norm_num) (zero_le_one.trans hC)
  refine ⟨B,C*B^K,hB,hA,?_⟩
  intro Q ρ m N σ J i F S hsep D E H hD hE hH hscale hEH f
  apply f.value_admissible Q ρ m N σ J i S (zero_lt_one.trans_le hA) hD (zero_le_one.trans hH)
  exact hcontrol Q ρ m N σ J i F id S (fun b => (f.jet b).order)
    (fun b => (f.jet b).vectors) hsep f.order_le
    (fun b _ => (f.jet b).norm_vectors) E H hE hH hscale hEH

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_JetStateGraph
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The profile graph estimate on the exact factorized state class

This packages the geometric hypotheses of the proved graph estimate. The
child envelope uses exactly the original list with anchors at most p
removed, and the same normalization and smooth multipliers.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable
open PlanarFalconer (PolicyDescriptor descriptorAnchor)
open scoped SchwartzMap

namespace JetStateGraphData
variable {n k : ℕ} {α B : ℝ}

 theorem symbol_parallel_test (G : JetStateGraphData n k α B) {K : ℕ}
    (f : DescriptorJetSymbol n K k G.F G.Dq) (A : ℝ)
    (X : List (Fin (n+2) → Bool)) (hX : X.length = G.a)
    (U : List (Fin (n+2) → Bool))
    (hU : U ∈ (G.Q.descendant X).occupiedPaths G.ρ (G.p-G.a)) :
    ∀ᵐ x ∂G.ρ.restrict ((G.Q.descendant X).descendant U).carrier,
    ∀ w : Sphere (n+2), G.symbol f A x w ≠ 0 →
      DyadicParallelTest (G.Q.descendant X) ((G.Q.descendant X).occupiedPaths G.ρ (G.p-G.a))
        (G.g-G.a) U w (angularTestWidth G.N G.σ G.J (G.i+1) G.p)
        ⌈((2:ℝ)^G.N)^(PlanarFalconer.height
          (profileExcess (d := n+2) G.profile G.N) G.g G.p+
            1000*(((n+2:ℕ):ℝ)+1)*G.σ)⌉₊ := by
  filter_upwards [ae_restrict_mem ((G.Q.descendant X).descendant U).measurable] with x hx
  intro w hw
  apply descriptorListGood_parallel_test G.Q G.unit G.ρ G.profile G.N G.σ G.J (G.i+1)
    G.F G.ag G.gp G.parallel X U hX ((mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hU).1) hx w
  intro b hb
  exact descriptorJetProduct_support G.Q G.ρ (fun t => G.profile (t/G.N)) G.N G.σ G.J G.i
    G.F id G.masks (fun b => (f.jet b).order) (fun b _ => (f.jet b).vectors) x w
    (mul_ne_zero_iff.mp hw).1 b hb

 theorem coefficient_nonneg (G : JetStateGraphData n k α B) : 0 ≤ G.coefficient := by
  unfold coefficient
  positivity

 theorem error_nonneg (G : JetStateGraphData n k α B) {H C W T : ℝ}
    (hH : 0 ≤ H) (hC : 0 ≤ C) (hW : 0 ≤ W) : 0 ≤ G.error H C W T := by
  have hcap := G.capBound_nonneg
  have hD := G.Dgraph_one
  have hτ := G.τ_pos
  unfold error capGraphError
  positivity

end JetStateGraphData
 theorem exists_jetState_graph_step
    (hpublished : PublishedGnomonicSurface) (n K k : ℕ) (hn : 1 ≤ n)
    (φ : 𝓢(ℝ, ℂ)) (Ψ : ℝ → ℝ)
    (hφ : ∀ u, φ u = (Ψ u : ℂ)) (hΨ : Measurable Ψ)
    (hpos : ∀ u, 0 ≤ Ψ u) (hzero : ∀ u ≤ 0, Ψ u = 0)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ t, Ψ t ≤ W)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4 : ℝ) 4)
    {α : ℝ} (hα : 0 < α) (T : ℝ)
    :
    ∃ B A H C : ℝ, 1 ≤ B ∧ 1 ≤ A ∧ 0 ≤ H ∧ 0 < C ∧
      ∀ G : JetStateGraphData n k α B,
      IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure G.v Ψ) →
      jetStateEnvelope n K k G.Dq G.F G.F G.Q G.ρ (fun t => G.profile (t/G.N))
        G.N G.σ G.J G.i G.masks A
        (G.ρ.restrict (G.Q.descendant G.X).carrier) (G.ρ.restrict (G.Q.descendant G.Y).carrier)
        (profileModelMass G.profile G.N G.a) (profileModelMass G.profile G.N G.a) G.a G.v Ψ ≤
      G.coefficient *
        (((descriptorJetBound (n+2) K)^K)^2 * ((descriptorJetBound (n+2) K)^K)^2 *
          G.childMaximum K A Ψ) + G.error H C W T := by
  obtain ⟨B,A,hB,hA,hadm⟩ := exists_descriptorJetSymbol_admissible n K k
  obtain ⟨H,C,hH,hC,hgraph⟩ := dyadic_profile_graph_energy_step hpublished n k hn
    φ Ψ hφ hΨ hpos hzero hW hΨW hsupp hα T
  refine ⟨B,A,H,C,hB,hA,hH,hC,?_⟩
  intro G hfinite
  let := hfinite
  let := G.regular.probability
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hQ : 0 < G.Q.side := by rw [G.unit]; norm_num
  have hMp : 0 < profileModelMass G.profile G.N G.p := by unfold profileModelMass; positivity
  have hsym (f : DescriptorJetSymbol n K k G.F G.Dq) :
      AngularAdmissible k G.Dgraph
        {z | ∀ b ∈ G.F, z ∈ descriptorEndpointGood G.Q G.ρ (fun t => G.profile (t/G.N))
          G.N G.σ G.J (G.i+1) b} (G.symbol f A) :=
    (hadm G.Q G.ρ (fun t => G.profile (t/G.N)) G.N G.σ G.J G.i G.F G.masks G.separated
      G.Dq G.Dmask G.Dsymbol G.Dq_nonneg G.Dmask_one G.Dsymbol_one G.mask_scale G.list_scale f).mono
      (add_nonneg G.Dq_nonneg (zero_le_one.trans G.Dsymbol_one)) G.symbol_scale (subset_refl _)
  have hchild0 : 0 ≤ ((descriptorJetBound (n+2) K)^K)^2 *
      ((descriptorJetBound (n+2) K)^K)^2 * G.childMaximum K A Ψ :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (childJetStateMaximum_nonneg n K k G.Dq _ G.Q G.ρ _ G.N G.σ G.J G.i G.masks A
        G.X G.Y (G.p-G.a) _ G.p G.v Ψ)
  apply csSup_le (show (jetStateValues n K k G.Dq G.F G.F G.Q G.ρ
    (fun t => G.profile (t/G.N)) G.N G.σ G.J G.i G.masks A
    (G.ρ.restrict (G.Q.descendant G.X).carrier) (G.ρ.restrict (G.Q.descendant G.Y).carrier)
    (profileModelMass G.profile G.N G.a) (profileModelMass G.profile G.N G.a)
    G.a G.v Ψ).Nonempty from ⟨0,Or.inl rfl⟩)
  intro h hh
  rcases hh with rfl | ⟨f,g,rfl⟩
  · exact add_nonneg (mul_nonneg G.coefficient_nonneg hchild0) (G.error_nonneg hH hC.le hW)
  · have hchild (row) (hr : row ∈ (G.Q.descendant G.X).occupiedPaths G.ρ (G.p-G.a) ×ˢ
        (G.Q.descendant G.Y).occupiedPaths G.ρ (G.p-G.a)) :
        independentAngularEnergy G.p G.v Ψ
          (fun z => endpointTransform (G.ρ.restrict ((G.Q.descendant G.X).descendant row.1).carrier)
            (profileModelMass G.profile G.N G.p) (G.symbol f A) z.1 z.2)
          (fun z => endpointTransform (G.ρ.restrict ((G.Q.descendant G.Y).descendant row.2).carrier)
            (profileModelMass G.profile G.N G.p) (G.symbol g A) z.1 z.2) ≤
        ((descriptorJetBound (n+2) K)^K)^2 * ((descriptorJetBound (n+2) K)^K)^2 *
          G.childMaximum K A Ψ :=
      childJetStateEnergy_le G.Q hQ G.ρ (fun t => G.profile (t/G.N))
        G.N G.σ G.J G.i G.masks G.separated hAp G.ap G.X G.Y G.X_length G.Y_length
        row hr hMp G.v Ψ f g
    have hresult := hgraph G.Q G.Q G.unit G.unit G.ρ G.ρ G.N G.s G.s G.lam
      G.profile G.profile G.regular G.regular G.N_pos
      G.a G.p G.g G.g G.σ G.ap G.pN G.σ_nonneg
      G.ag G.gp G.gap G.ag G.gp G.gap G.X G.Y G.X_length G.Y_length
      G.v G.τ G.δ G.capBound 1 G.Dgraph G.τ_pos G.δ_pos G.δ_small
      G.capBound_nonneg (by norm_num) G.Dgraph_one G.cap_scale G.endpoint_scale G.phase_error
      G.frequency G.test_scale G.caps id G.partition G.cap_control G.cap_nonneg G.partition_one
      (G.symbol f A) (G.symbol g A) (hsym f).1 (hsym g).1
      (angularTestWidth G.N G.σ G.J (G.i+1) G.p)
      (angularTestWidth G.N G.σ G.J (G.i+1) G.p) G.left_width G.right_width
      (G.symbol_parallel_test f A G.X G.X_length) (G.symbol_parallel_test g A G.Y G.Y_length)
      _ hchild0 hchild
    have hexcess : profileExcess (d := n+2) G.profile G.N =
        (fun j : ℕ => G.profile ((j:ℝ)/G.N)-((n+2:ℕ):ℝ)/2*(j:ℝ)/G.N) := rfl
    simpa only [jetStateEnergy,JetStateGraphData.symbol,JetStateGraphData.coefficient,
      JetStateGraphData.error,hexcess,min_self,add_assoc] using hresult

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PolicyPrefixScales
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual high-prefix shell supplies the graph scales -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor policyDepth)

theorem policy_prefix_inverse_scales {m : ℕ} (P : PolicyJetData m)
    (hσ : 0 < P.σ) (hleft : P.a₀ = P.a)
    (hwide : P.a+100*P.q < P.t₀) (hq : P.σ*(P.N:ℝ) ≤ P.q)
    (hhigh : (P.t₀:ℝ) ≤ P.t+P.σ*P.N) :
    20*P.σ*(P.N:ℝ) ≤ (P.t:ℝ)-P.a ∧
      (P.longest:ℝ) ≤ ((P.t:ℝ)-P.a)/2+P.σ*P.N := by
  have hwideR : (P.a:ℝ)+100*P.q < P.t₀ := by exact_mod_cast hwide
  have hσN : 0 ≤ P.σ*(P.N:ℝ) := mul_nonneg hσ.le (Nat.cast_nonneg _)
  have hlong : P.longest ≤ (P.t₀-P.a)/2 := by
    apply Finset.sup_le
    intro b hb
    have hb' := (Finset.mem_filter.mp hb).1
    rw [hleft] at hb'
    exact PlanarFalconer.policyDescriptor_length_le_half P.policy P.q_pos hb'
  have hlongR : 2*(P.longest:ℝ) ≤ (P.t₀:ℝ)-P.a := by
    have hh : P.a+2*P.longest ≤ P.t₀ := by omega
    have hhR : (P.a:ℝ)+2*P.longest ≤ P.t₀ := by exact_mod_cast hh
    linarith
  constructor <;> nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_DyadicRowCount
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting the original dyadic rows at the terminal scale -/

namespace Falconer
open MeasureTheory

theorem dyadic_row_count_le {d j : ℕ} (Q₁ Q₂ : DyadicCube d)
    (μ ν : Measure (Space d)) {R : ℝ} (hR : 0 ≤ R) (hj : (2 : ℝ)^j ≤ R) :
    ((Q₁.occupiedPaths μ j ×ˢ Q₂.occupiedPaths ν j).card : ℝ) ≤ R^(2*d) := by
  have hc (Q : DyadicCube d) (ρ : Measure (Space d)) :
      ((Q.occupiedPaths ρ j).card : ℝ) ≤ R^d := by
    calc
      _ ≤ (2 : ℝ)^(d*j) := by exact_mod_cast Q.card_occupiedPaths_le ρ j
      _ = ((2 : ℝ)^j)^d := by rw [← pow_mul,Nat.mul_comm]
      _ ≤ R^d := pow_le_pow_left₀ (by positivity) hj d
  rw [Finset.card_product,Nat.cast_mul]
  calc
    _ ≤ R^d*R^d := mul_le_mul (hc Q₁ μ) (hc Q₂ ν) (by positivity) (pow_nonneg hR d)
    _ = R^(2*d) := by rw [← pow_add]; congr 1; omega

theorem dyadic_row_count_at_terminal_depth {d j N : ℕ} (Q₁ Q₂ : DyadicCube d)
    (μ ν : Measure (Space d)) (hj : j ≤ N) :
    ((Q₁.occupiedPaths μ j ×ˢ Q₂.occupiedPaths ν j).card : ℝ) ≤ ((2 : ℝ)^N)^(2*d) :=
  dyadic_row_count_le Q₁ Q₂ μ ν (by positivity) (pow_le_pow_right₀ (by norm_num) hj)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_GraphTwoErrors
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Paying for both graph localization errors

The perpendicular error has an arbitrary derivative-order gain. The radial
error has an independent arbitrary Schwartz-decay order. Both pay for the
cap pairs, cell pairs and model-mass normalization with the same 11d cost.
-/

namespace Falconer

theorem graph_two_errors_absorption (d : ℕ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ) (minOrder : ℕ := 0) :
    ∃ m : ℕ, minOrder ≤ m ∧ ∀ {R K S P I A B C₁ C₂ q : ℝ},
      1 ≤ R → 0 ≤ K → 0 ≤ S → 0 ≤ P → 0 ≤ I → 0 ≤ A → 0 ≤ B →
      0 ≤ C₁ → 0 ≤ C₂ → 0 ≤ q →
      K ≤ A*R^d → S ≤ R^(2*d) → P*I ≤ R^(5*d) → q ≤ B*R^(-(26*σ)) →
      P*K^2*S^2*(I*(C₁*q^m+C₂*R^(-(T+(11*d : ℕ))))) ≤
        A^2*(C₁*B^m+C₂)*R^(-T) := by
  obtain ⟨m,hmin,hm⟩ := positive_power_gain_order_ge (by positivity : 0 < 26*σ) (↑(11*d : ℕ) : ℝ) T minOrder
  refine ⟨m,hmin,?_⟩
  intro R K S P I A B C₁ C₂ q hR hK hS hP hI hA hB hC₁ hC₂ hq hKbound hSbound hPI hqbound
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hcost : P*K^2*S^2*I ≤ A^2*R^(11*d) := by
    calc
      _ = (P*I)*K^2*S^2 := by ring
      _ ≤ R^(5*d)*(A*R^d)^2*(R^(2*d))^2 := by gcongr
      _ = A^2*(R^(5*d)*(R^d)^2*(R^(2*d))^2) := by ring
      _ = _ := by
        congr 1
        rw [← pow_mul,← pow_mul,← pow_add,← pow_add]
        congr 1
        omega
  have hgain : R^(11*d)*q^m ≤ B^m*R^(-T) := by
    simpa only [Real.rpow_natCast] using hm hR hB hq hqbound
  have hrad : R^(11*d)*R^(-(T+(11*d : ℕ))) = R^(-T) := by
    rw [← Real.rpow_natCast,← Real.rpow_add hR0]
    congr 1
    ring
  calc
    _ = (P*K^2*S^2*I) * (C₁*q^m + C₂*R^(-(T+(11*d : ℕ)))) := by ring
    _ ≤ (A^2*R^(11*d)) * (C₁*q^m + C₂*R^(-(T+(11*d : ℕ)))) :=
      mul_le_mul_of_nonneg_right hcost (by positivity)
    _ = A^2 * (C₁*(R^(11*d)*q^m) + C₂*(R^(11*d)*R^(-(T+(11*d : ℕ))))) := by ring
    _ ≤ A^2 * (C₁*(B^m*R^(-T)) + C₂*R^(-T)) := by rw [hrad]; gcongr
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_GraphEnergyError
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Arbitrary power decay of the explicit graph-energy error

The derivative order is chosen first. The constants obtained at that order
may then be used in the uniform graph estimate. Both cap and row counts,
and the four model-mass inverses, are included in the polynomial cost.
-/

namespace Falconer
open Set MeasureTheory

theorem capGraphError_arbitrary_power (d : ℕ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ) (minOrder : ℕ := 0) :
    ∃ m : ℕ, minOrder ≤ m ∧ ∀ {A C W H B : ℝ},
      0 ≤ A → 0 ≤ C → 0 ≤ W → 0 ≤ H → 0 ≤ B →
      ∀ {R P M₁ M₂ D v τ Cap Q : ℝ} {K S : ℕ},
      1 ≤ R → 0 ≤ P → 0 ≤ D → 0 < τ → 0 ≤ Cap → 0 ≤ Q →
      (K : ℝ) ≤ Cap*R^d → (S : ℝ) ≤ R^(2*d) →
      P*|(M₁⁻¹*M₁⁻¹)*(M₂⁻¹*M₂⁻¹)| ≤ R^(5*d) →
      16*D/((2 : ℝ)^v*τ) ≤ Q*R^(-(26*σ)) →
      P*capGraphError d m A C W R (T+(11*d : ℕ)) M₁ M₂ H B D v τ K S ≤
        Cap^2 *
          ((A*(4^m*H*B*B)*(B*B)*(sphereMeasure d).real univ*(4*W))*Q^m +
            (B*B)*(B*B)*C*((sphereMeasure d).real univ)^2) * R^(-T) := by
  obtain ⟨m,hmin,hm⟩ := graph_two_errors_absorption d hσ T minOrder
  refine ⟨m,hmin,?_⟩
  intro A C W H B hA hC hW hH hB R P M₁ M₂ D v τ Cap Q K S
    hR hP hD hτ hCap hQ hK hS hmass hratio
  have hmain := hm hR (Nat.cast_nonneg K) (Nat.cast_nonneg S) hP
    (abs_nonneg ((M₁⁻¹*M₁⁻¹)*(M₂⁻¹*M₂⁻¹))) hCap hQ
    (show 0 ≤ A*(4^m*H*B*B)*(B*B)*(sphereMeasure d).real univ*(4*W) by positivity)
    (show 0 ≤ (B*B)*(B*B)*C*((sphereMeasure d).real univ)^2 by positivity)
    (show 0 ≤ 16*D/((2 : ℝ)^v*τ) by positivity) hK hS hmass hratio
  convert hmain using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [capGraphError]
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_ProfileGraphBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The model masses pay for both graph errors

The child masses cancel before estimating. Only the two parent profile
values remain, so the combined normalization costs at most R^(5d).
-/

namespace Falconer

theorem graph_error_mass_cancellation {M₁ M₂ U₁ U₂ : ℝ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hU₁ : 0 < U₁) (hU₂ : 0 < U₂) :
    ((U₁/M₁)*(U₂/M₂))^2 * |(U₁⁻¹*U₁⁻¹)*(U₂⁻¹*U₂⁻¹)| =
      (M₁⁻¹)^2*(M₂⁻¹)^2 := by
  rw [abs_of_pos (by positivity)]
  field_simp

theorem profile_graph_error_weight_bound (d : ℕ) {N a p : ℕ}
    (hN : 0 < N) (m₁ m₂ : ℝ → ℝ) {v : ℝ} (hv : v ≤ N)
    (hm₁ : m₁ ((a:ℝ)/N) ≤ d) (hm₂ : m₂ ((a:ℝ)/N) ≤ d) :
    (2:ℝ)^((d:ℝ)*(v-a)) *
        ((profileModelMass m₁ N p/profileModelMass m₁ N a)*
          (profileModelMass m₂ N p/profileModelMass m₂ N a))^2 *
        |((profileModelMass m₁ N p)⁻¹*(profileModelMass m₁ N p)⁻¹)*
          ((profileModelMass m₂ N p)⁻¹*(profileModelMass m₂ N p)⁻¹)| ≤
      ((2:ℝ)^N)^(5*(d:ℝ)) := by
  have hM (m : ℝ → ℝ) (j : ℕ) : 0 < profileModelMass m N j := by
    unfold profileModelMass
    positivity
  have hR : 0 < (2:ℝ)^N := by positivity
  have hRone : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  have hm (m : ℝ → ℝ) : ((profileModelMass m N a)⁻¹)^2 =
      ((2:ℝ)^N)^(2*m ((a:ℝ)/N)) := by
    unfold profileModelMass
    rw [← Real.rpow_neg hR.le,← Real.rpow_natCast,← Real.rpow_mul hR.le]
    congr 1
    ring
  rw [mul_assoc,graph_error_mass_cancellation (hM m₁ a) (hM m₂ a) (hM m₁ p) (hM m₂ p),
    hm m₁,hm m₂,← dyadic_rpow_change_base hN ((d:ℝ)*(v-a)),
    ← mul_assoc,← Real.rpow_add hR,← Real.rpow_add hR]
  apply Real.rpow_le_rpow_of_exponent_le hRone
  have hNR : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  have hfrac : (d:ℝ)*(v-a)/N ≤ d := by
    apply (div_le_iff₀ hNR).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) d,Nat.cast_nonneg (α := ℝ) a]
  linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_ProfileGraphError
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Arbitrary-power error for the normalized profile graph estimate -/

namespace Falconer
open MeasureTheory

theorem profile_graph_error_arbitrary_power (d : ℕ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ) (minOrder : ℕ := 0) :
    ∃ k : ℕ, minOrder ≤ k ∧ ∀ {A C W H B : ℝ},
      0 ≤ A → 0 ≤ C → 0 ≤ W → 0 ≤ H → 0 ≤ B →
      ∀ (Q₁ Q₂ : DyadicCube d) (ρ₁ ρ₂ : Measure (Space d))
        (m₁ m₂ : ℝ → ℝ) (N a p : ℕ), 0 < N → a ≤ p → p ≤ N →
      m₁ ((a:ℝ)/N) ≤ d → m₂ ((a:ℝ)/N) ≤ d →
      ∀ {D v τ Cap Z : ℝ} {K : ℕ},
      0 ≤ D → v ≤ N → 0 < τ → 0 ≤ Cap → 0 ≤ Z →
      (K:ℝ) ≤ Cap*((2:ℝ)^N)^d →
      16*D/((2:ℝ)^v*τ) ≤ Z*((2:ℝ)^N)^(-(26*σ)) →
      (2:ℝ)^((d:ℝ)*(v-a)) *
        ((profileModelMass m₁ N p/profileModelMass m₁ N a)*
          (profileModelMass m₂ N p/profileModelMass m₂ N a))^2 *
        capGraphError d k A C W ((2:ℝ)^N) (T+(11*d:ℕ))
          (profileModelMass m₁ N p) (profileModelMass m₂ N p) H B D v τ K
          (Q₁.occupiedPaths ρ₁ (p-a) ×ˢ Q₂.occupiedPaths ρ₂ (p-a)).card ≤
      Cap^2 *
        ((A*(4^k*H*B*B)*(B*B)*(sphereMeasure d).real Set.univ*(4*W))*Z^k +
          (B*B)*(B*B)*C*((sphereMeasure d).real Set.univ)^2) * ((2:ℝ)^N)^(-T) := by
  obtain ⟨k,hmin,hk⟩ := capGraphError_arbitrary_power d hσ T minOrder
  refine ⟨k,hmin,?_⟩
  intro A C W H B hA hC hW hH hB Q₁ Q₂ ρ₁ ρ₂ m₁ m₂ N a p hN hap hp
    hm₁ hm₂ D v τ Cap Z K hD hv hτ hCap hZ hK hratio
  have hmass := profile_graph_error_weight_bound d (p := p) hN m₁ m₂ hv hm₁ hm₂
  have hrows := dyadic_row_count_at_terminal_depth Q₁ Q₂ ρ₁ ρ₂
    (show p-a ≤ N by omega)
  have hmass' : (2:ℝ)^((d:ℝ)*(v-a)) *
      ((profileModelMass m₁ N p/profileModelMass m₁ N a)*
        (profileModelMass m₂ N p/profileModelMass m₂ N a))^2 *
        |((profileModelMass m₁ N p)⁻¹*(profileModelMass m₁ N p)⁻¹)*
          ((profileModelMass m₂ N p)⁻¹*(profileModelMass m₂ N p)⁻¹)| ≤
        ((2:ℝ)^N)^(5*d) := by
    have he : (5:ℝ)*(d:ℝ) = ((5*d:ℕ):ℝ) := by simp only [Nat.cast_mul,Nat.cast_ofNat]
    rw [he,Real.rpow_natCast] at hmass
    exact hmass
  exact hk hA hC hW hH hB (one_le_pow₀ (by norm_num))
    (by positivity) hD hτ hCap hZ hK hrows hmass' hratio

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_PolicyGraphError
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cap counts and error orders for the actual policy graph step -/

namespace Falconer
open Set MeasureTheory

theorem policyGraphRadius_inv_bound {N a p : ℕ} {σ c₀ : ℝ}
    (hp : p ≤ N) (hσ : 0 ≤ σ) (hc₀ : 0 < c₀) :
    (policyGraphRadius N a p σ c₀)⁻¹ ≤ (c₀⁻¹+1)*(2:ℝ)^N := by
  have hR : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  have hexp : -(N:ℝ) ≤ (a:ℝ)-p+10*σ*N := by
    have hp' : (p:ℝ) ≤ N := by exact_mod_cast hp
    have ha : (0:ℝ) ≤ a := Nat.cast_nonneg a
    have hh : 0 ≤ 10*σ*(N:ℝ) := by positivity
    linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hexp
  have hinv : ((2:ℝ)^((a:ℝ)-p+10*σ*N))⁻¹ ≤ (2:ℝ)^N := by
    have hh := (inv_le_inv₀ (by positivity : 0 < (2:ℝ)^((a:ℝ)-p+10*σ*N))
      (by positivity : 0 < (2:ℝ)^(-(N:ℝ)))).mpr hpow
    simpa only [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),inv_inv,
      Real.rpow_natCast] using hh
  have hc : c₀⁻¹ ≤ (c₀⁻¹+1)*(2:ℝ)^N := by
    have hh := mul_le_mul_of_nonneg_left hR (show 0 ≤ c₀⁻¹+1 by positivity)
    nlinarith [inv_pos.mpr hc₀]
  have hr : (2:ℝ)^N ≤ (c₀⁻¹+1)*(2:ℝ)^N := by
    nlinarith [inv_pos.mpr hc₀,pow_pos (by norm_num : (0:ℝ) < 2) N]
  unfold policyGraphRadius
  by_cases h : c₀ ≤ (2:ℝ)^((a:ℝ)-p+10*σ*N)
  · simpa only [min_eq_left h] using hc
  · simpa only [min_eq_right (le_of_not_ge h)] using hinv.trans hr

theorem policyGraphCap_count {d N a p : ℕ} {σ c₀ : ℝ}
    (hp : p ≤ N) (hσ : 0 ≤ σ) (hc₀ : 0 < c₀) {K : ℕ}
    (hK : (K:ℝ) ≤ (4/policyGraphRadius N a p σ c₀+1)^d) :
    (K:ℝ) ≤ (4*c₀⁻¹+5)^d*((2:ℝ)^N)^d := by
  have hi := policyGraphRadius_inv_bound (a := a) hp hσ hc₀
  have hR : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  have hδ : 0 < policyGraphRadius N a p σ c₀ :=
    lt_min hc₀ (by positivity)
  calc
    _ ≤ (4/policyGraphRadius N a p σ c₀+1)^d := hK
    _ ≤ ((4*c₀⁻¹+5)*(2:ℝ)^N)^d := by
      apply pow_le_pow_left₀ (by positivity)
      rw [div_eq_mul_inv]
      nlinarith
    _ = _ := mul_pow _ _ _

theorem exists_policy_graph_error_order (m : ℕ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ) (minOrder : ℕ := 0) :
    ∃ k : ℕ, minOrder ≤ k ∧ ∀ {α B H C W Cap V : ℝ},
      0 ≤ H → 0 ≤ C → 0 ≤ W → 0 ≤ Cap → 0 ≤ V →
      ∀ G : JetStateGraphData (m+1) k α B,
      G.v ≤ G.N →
      (G.caps.card:ℝ) ≤ Cap*((2:ℝ)^G.N)^(m+3) →
      16*G.Dgraph/((2:ℝ)^G.v*G.τ) ≤ V*((2:ℝ)^G.N)^(-(26*σ)) →
      G.error H C W (T+(11*(m+3):ℕ)) ≤
        Cap^2*((H*(4^k*G.capBound)*(sphereMeasure (m+3)).real univ*(4*W))*V^k+
          C*((sphereMeasure (m+3)).real univ)^2)*((2:ℝ)^G.N)^(-T) := by
  obtain ⟨k,hmin,hk⟩ := profile_graph_error_arbitrary_power (m+3) hσ T minOrder
  refine ⟨k,hmin,?_⟩
  intro α B H C W Cap V hH hC hW hCap hV G hv hcard hratio
  have hm : G.profile ((G.a:ℝ)/G.N) ≤ (m+3:ℕ) :=
    (G.regular.range _ ⟨by positivity,by
      apply (div_le_one (Nat.cast_pos.mpr G.N_pos)).mpr
      exact_mod_cast G.ap.trans G.pN⟩).2
  have hh := hk hH hC hW G.capBound_nonneg (by norm_num : (0:ℝ) ≤ 1)
    (G.Q.descendant G.X) (G.Q.descendant G.Y) G.ρ G.ρ G.profile G.profile
    G.N G.a G.p G.N_pos G.ap G.pN hm hm
    (zero_le_one.trans G.Dgraph_one) hv G.τ_pos hCap hV hcard hratio
  simpa only [JetStateGraphData.error,mul_one,one_mul,mul_assoc] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_PolicyGraphAtStep
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform graph reduction at the direct or high-prefix geometry -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap

theorem exists_policy_graph_step_at
    (hpublished : PublishedGnomonicSurface) (m K : ℕ)
    {σ : ℝ} (hσ : 0 < σ) {J : ℕ} (hJ : 0 < J) (T : ℝ)
    (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ)
    (hφ : ∀ u, φ u = (Ψ u : ℂ)) (hΨ : Measurable Ψ)
    (hpos : ∀ u, 0 ≤ Ψ u) (hzero : ∀ u ≤ 0, Ψ u = 0)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ u, Ψ u ≤ W)
    (hsupp : ∀ u, Ψ u ≠ 0 → u ∈ Ioo (1/4:ℝ) 4) (minOrder : ℕ := 0) :
    ∃ (L : ℕ) (Z : ℝ) (N₀ : ℕ), minOrder ≤ L ∧ 1 ≤ Z ∧
      ∀ (P : PolicyJetData m), P.σ = σ → P.J = J → P.Z = Z →
      N₀ ≤ P.N → P.i+1 ≤ P.J →
      ∀ geometry : P.GraphGeometry,
      P.envelope K L Ψ ≤ P.graphCoefficient geometry.p*
        (((descriptorJetBound (m+3) K)^K)^2*((descriptorJetBound (m+3) K)^K)^2*
          P.graphChild K L geometry.p Ψ)+((2:ℝ)^P.N)^(-T) := by
  obtain ⟨k,hmin,herr⟩ := exists_policy_graph_error_order m hσ (T+1) minOrder
  obtain ⟨B,Z,H,C,hB,hZ,hH,hC,hgraph⟩ := exists_jetState_graph_step hpublished
    (m+1) K k (by omega) φ Ψ hφ hΨ hpos hzero hW hΨW hsupp
    (by positivity : 0 < 20*σ) (T+1+(11*(m+3):ℕ))
  obtain ⟨Hcap,hHcap,hcaps⟩ := exists_controlled_cap_partition (m+1) k
  let c₀ : ℝ := 1/4
  let Cgeo : ℝ := 1+4*Real.sqrt (m+3:ℕ)
  let Cap : ℝ := (4*c₀⁻¹+5)^(m+3)
  let V : ℝ := 16*Cgeo*(4+c₀⁻¹)
  let E : ℝ := Cap^2*((H*(4^k*Hcap)*(sphereMeasure (m+3)).real univ*(4*W))*V^k+
    C*((sphereMeasure (m+3)).real univ)^2)
  obtain ⟨Nerr,hNerr⟩ := Regularization.fixed_constant_absorbed (by norm_num : (0:ℝ) < 1) E
  obtain ⟨Nlarge,hNlarge⟩ := Regularization.fixed_constant_absorbed
    (by positivity : 0 < 20*σ) (40*Real.sqrt (m+3:ℕ)+4*Real.pi)
  let Nlist := Classical.choose (eventual_descriptor_list_scale 3 hB hσ)
  let Nwidth := Classical.choose (uniform_graph_parallel_width (m+3) hσ hJ)
  refine ⟨k,Z,max (max Nerr Nlarge) (max Nlist Nwidth),hmin,hZ,?_⟩
  intro P hσP hJP hZP hN hi geometry
  have hNerrP : Nerr ≤ P.N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hNlargeP : Nlarge ≤ P.N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hNlistP : Nlist ≤ P.N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNwidthP : Nwidth ≤ P.N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hpσ : 0 < P.σ := by simpa only [hσP] using hσ
  have hpJ : 0 < P.J := by simpa only [hJP] using hJ
  have hnlist : Classical.choose (eventual_descriptor_list_scale 3 hB hpσ) ≤ P.N := by
    simpa only [hσP] using hNlistP
  have hnwidth : Classical.choose (uniform_graph_parallel_width (m+3) hpσ hpJ) ≤ P.N := by
    simpa only [hσP,hJP] using hNwidthP
  have hlarge := hNlarge P.N hNlargeP
  have hlarge₁ : 40*Real.sqrt (m+3:ℕ) ≤ ((2:ℝ)^P.N)^(20*P.σ) := by
    rw [hσP]
    linarith [Real.pi_pos]
  have hlarge₂ : 4*Real.pi ≤ ((2:ℝ)^P.N)^(20*P.σ) := by
    rw [hσP]
    linarith [Real.sqrt_nonneg (m+3:ℕ)]
  have hc₀ : 0 < c₀ := by norm_num [c₀]
  have hcsmall : c₀ ≤ 1/2 := by norm_num [c₀]
  have hCgeo : 1 ≤ Cgeo := by dsimp [Cgeo]; linarith [Real.sqrt_nonneg (m+3:ℕ)]
  have hCdim : 4*Real.sqrt (m+3:ℕ) ≤ Cgeo := by dsimp [Cgeo]; linarith
  have hpN : geometry.p ≤ P.N := geometry.pN
  have hscale := policy_graph_scale_data (m+3) P.N_pos hpσ hc₀ hcsmall hCgeo hCdim
    geometry.depth geometry.length geometry.frequency hlarge₁ hlarge₂
  obtain ⟨S,η,hcard,hone,hnonneg,hcontrol⟩ := hcaps
    (policyGraphRadius P.N P.a geometry.p P.σ c₀) hscale.1
    (hscale.2.1.trans (by norm_num))
  let G := P.graphDataAt k B hB hpσ hpJ hi hnlist hnwidth geometry c₀ Cgeo Hcap
    hc₀ hcsmall hCgeo hCdim hHcap hlarge₁ hlarge₂ S η hcontrol hnonneg hone
  have hGN : G.N = P.N := rfl
  have hcap : (G.caps.card:ℝ) ≤ Cap*((2:ℝ)^G.N)^(m+3) :=
    policyGraphCap_count hpN hpσ.le hc₀ hcard
  have hratio : 16*G.Dgraph/((2:ℝ)^G.v*G.τ) ≤ V*((2:ℝ)^G.N)^(-(26*σ)) := by
    change 16*policyGraphScale P.N P.a geometry.p P.longest P.σ c₀ Cgeo /
      ((2:ℝ)^(P.t:ℝ)*policyGraphWidth P.N geometry.p P.σ) ≤ _
    simpa only [V,hσP,Real.rpow_natCast,hGN,neg_mul] using hscale.2.2.2.2.2.2.2.2
  have htN : G.v ≤ G.N := Nat.cast_le.mpr (P.base_right.trans P.base_N)
  have he := herr hH hC.le hW (show 0 ≤ Cap by dsimp [Cap]; positivity)
    (show 0 ≤ V by dsimp [V]; positivity) G htN hcap hratio
  have he' : G.error H C W (T+1+(11*(m+3):ℕ)) ≤ ((2:ℝ)^P.N)^(-T) := by
    apply he.trans
    change E*((2:ℝ)^P.N)^(-(T+1)) ≤ _
    calc
      _ ≤ ((2:ℝ)^P.N)^1*((2:ℝ)^P.N)^(-(T+1)) :=
        mul_le_mul_of_nonneg_right (hNerr P.N hNerrP) (by positivity)
      _ = _ := by rw [← Real.rpow_add (by positivity : 0 < (2:ℝ)^P.N)]; congr 1; ring
  have hfinite := PlanarFalconer.sourceAngularShellMeasure_finite (P.t:ℝ) Ψ hW hΨW
    (fun u hu => by
      by_contra hn
      exact (not_lt_of_ge hu.le) (hsupp u hn).2)
  rw [← hσP] at hgraph
  have hg := hgraph G hfinite
  rw [← hZP] at hg
  change P.envelope K k Ψ ≤ P.graphCoefficient geometry.p*
    (((descriptorJetBound (m+3) K)^K)^2*((descriptorJetBound (m+3) K)^K)^2*
      P.graphChild K k geometry.p Ψ)+G.error H C W (T+1+(11*(m+3):ℕ)) at hg
  exact hg.trans (add_le_add le_rfl he')

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_PolicyJetChildren
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual policy states at the child cells of an angular step -/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

namespace PolicyJetData
variable {m : ℕ}

theorem child_envelope (P : PolicyJetData m) (K L p : ℕ) (hap : P.a ≤ p)
    (row : List (Fin (m+3) → Bool) × List (Fin (m+3) → Bool))
    (hrow : row ∈ (P.Q.descendant P.X).occupiedPaths P.ρ (p-P.a) ×ˢ
      (P.Q.descendant P.Y).occupiedPaths P.ρ (p-P.a)) (Ψ : ℝ → ℝ) :
    (P.child p hap row hrow).envelope K L Ψ =
      jetStateEnvelope (m+1) K L 1
        (P.list.filter (fun b => p < PlanarFalconer.descriptorAnchor b))
        (P.list.filter (fun b => p < PlanarFalconer.descriptorAnchor b))
        P.Q P.ρ (fun t => P.profile (t/P.N)) P.N P.σ P.J P.i P.masks P.Z
        (P.ρ.restrict ((P.Q.descendant P.X).descendant row.1).carrier)
        (P.ρ.restrict ((P.Q.descendant P.Y).descendant row.2).carrier)
        (profileModelMass P.profile P.N p) (profileModelMass P.profile P.N p) p P.t Ψ := by
  simp only [envelope,child,list,DyadicCube.descendant_append,
    PlanarFalconer.remainingPolicyDescriptors_drop P.policy P.N P.q P.a₀ P.t₀ hap]

theorem graphChild_le (P : PolicyJetData m) (K L p : ℕ) (hap : P.a ≤ p)
    (Ψ : ℝ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hchild : ∀ row, ∀ hrow : row ∈
      (P.Q.descendant P.X).occupiedPaths P.ρ (p-P.a) ×ˢ
        (P.Q.descendant P.Y).occupiedPaths P.ρ (p-P.a),
      (P.child p hap row hrow).envelope K L Ψ ≤ M) :
    P.graphChild K L p Ψ ≤ M := by
  apply finiteEnvelopeMaximum_le _ _ hM
  intro row hrow
  simpa only [child_envelope] using hchild row hrow

end PolicyJetData
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PolicyBranchCoefficients
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dimension-dependent coefficient payments in the scalar branch ledger -/

namespace Falconer
open Set MeasureTheory

theorem graph_loss_le_branch_reserve (d : ℕ) {lam σ : ℝ}
    (hlam : 0 ≤ lam) (hσ : 0 ≤ σ) :
    (1000*((d:ℝ)+1)+32*d)*σ+4*((d:ℝ)+1)*lam ≤
      4000*(dimensionalBranchReserve d lam σ+σ) := by
  unfold dimensionalBranchReserve
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hlam,
    mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hσ]

private theorem absorbed_power_coefficient {ε : ℝ} (hε : 0 < ε) (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x y z : ℝ, y ≤ z →
      C*((2:ℝ)^N)^(x+y) ≤ ((2:ℝ)^N)^(x+z+ε) := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hε C
  refine ⟨N₀,?_⟩
  intro N hN x y z hyz
  calc
    _ ≤ ((2:ℝ)^N)^ε*((2:ℝ)^N)^(x+y) :=
      mul_le_mul_of_nonneg_right (hN₀ N hN) (by positivity)
    _ = ((2:ℝ)^N)^(ε+(x+y)) := (Real.rpow_add (by positivity) _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le
      (one_le_pow₀ (by norm_num)) (by linarith)

theorem eventual_policy_graph_coefficient (m K : ℕ) {lam σ ε : ℝ}
    (hlam : 0 ≤ lam) (hσ : 0 ≤ σ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ P : PolicyJetData m, P.lam = lam → P.σ = σ → N₀ ≤ P.N →
      ∀ p : ℕ,
      P.graphCoefficient p *
        (((descriptorJetBound (m+3) K)^K)^2*((descriptorJetBound (m+3) K)^K)^2) ≤
      ((2:ℝ)^P.N)^(-2*(profileExcess (d := m+3) P.profile P.N p-
        profileExcess (d := m+3) P.profile P.N P.a)+
        PlanarFalconer.height (profileExcess (d := m+3) P.profile P.N) P.a p+
        4000*(dimensionalBranchReserve (m+3) lam σ+σ)+ε) := by
  let C : ℝ := 2*11^(m+3)*
    (((descriptorJetBound (m+3) K)^K)^2*((descriptorJetBound (m+3) K)^K)^2)
  obtain ⟨N₀,hN₀⟩ := absorbed_power_coefficient hε C
  refine ⟨N₀,?_⟩
  intro P hLam hσP hN p
  have he := hN₀ P.N hN
    (-2*(profileExcess (d := m+3) P.profile P.N p-
      profileExcess (d := m+3) P.profile P.N P.a)+
      PlanarFalconer.height (profileExcess (d := m+3) P.profile P.N) P.a p)
    ((1000*(((m+3:ℕ):ℝ)+1)+32*(m+3:ℕ))*σ+4*(((m+3:ℕ):ℝ)+1)*lam)
    (4000*(dimensionalBranchReserve (m+3) lam σ+σ))
    (graph_loss_le_branch_reserve (m+3) hlam hσ)
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  unfold PolicyJetData.graphCoefficient C
  rw [hLam,hσP]
  have hexp :
      -(profileExcess (d := m+3) P.profile P.N p-profileExcess (d := m+3) P.profile P.N P.a)-
        (profileExcess (d := m+3) P.profile P.N p-profileExcess (d := m+3) P.profile P.N P.a)+
        PlanarFalconer.height (profileExcess (d := m+3) P.profile P.N) P.a p+
        (1000*(((m+3:ℕ):ℝ)+1)+32*(m+3:ℕ))*σ+4*(((m+3:ℕ):ℝ)+1)*lam =
      -2*(profileExcess (d := m+3) P.profile P.N p-profileExcess (d := m+3) P.profile P.N P.a)+
        PlanarFalconer.height (profileExcess (d := m+3) P.profile P.N) P.a p+
        ((1000*(((m+3:ℕ):ℝ)+1)+32*(m+3:ℕ))*σ+4*(((m+3:ℕ):ℝ)+1)*lam) := by ring
  rw [hexp]
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_PolicyGraphAtRecurrence
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The weighted graph recurrence at either policy geometry -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap

theorem exists_policy_graph_recurrence_at
    (hpublished : PublishedGnomonicSurface) (m K : ℕ)
    {lam σ ε : ℝ} (hlam : 0 ≤ lam) (hσ : 0 < σ) (hε : 0 < ε)
    {J : ℕ} (hJ : 0 < J) (T : ℝ)
    (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ)
    (hφ : ∀ u, φ u = (Ψ u : ℂ)) (hΨ : Measurable Ψ)
    (hpos : ∀ u, 0 ≤ Ψ u) (hzero : ∀ u ≤ 0, Ψ u = 0)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ u, Ψ u ≤ W)
    (hsupp : ∀ u, Ψ u ≠ 0 → u ∈ Ioo (1/4:ℝ) 4) (minOrder : ℕ) :
    ∃ (L : ℕ) (Z : ℝ) (N₀ : ℕ), minOrder ≤ L ∧ 1 ≤ Z ∧
      ∀ (P : PolicyJetData m), P.lam = lam → P.σ = σ → P.J = J → P.Z = Z →
      N₀ ≤ P.N → P.i+1 ≤ P.J → ∀ geometry : P.GraphGeometry,
      ∀ M : ℝ, 0 ≤ M →
      (∀ row, ∀ hrow : row ∈
        (P.Q.descendant P.X).occupiedPaths P.ρ (geometry.p-P.a) ×ˢ
          (P.Q.descendant P.Y).occupiedPaths P.ρ (geometry.p-P.a),
        P.directWeight geometry.p lam σ ε *
          (P.child geometry.p geometry.ap row hrow).envelope K L Ψ ≤ M) →
      P.envelope K L Ψ ≤ M+((2:ℝ)^P.N)^(-T) := by
  obtain ⟨L,Z,Ngraph,hL,hZ,hgraph⟩ := exists_policy_graph_step_at hpublished m K hσ hJ T
    φ Ψ hφ hΨ hpos hzero hW hΨW hsupp minOrder
  obtain ⟨Ncoeff,hcoeff⟩ := eventual_policy_graph_coefficient m K hlam hσ.le hε
  refine ⟨L,Z,max Ngraph Ncoeff,hL,hZ,?_⟩
  intro P hLam hσP hJP hZP hN hi geometry M hM hchildren
  let w := P.directWeight geometry.p lam σ ε
  have hw : 0 < w := by dsimp [w,PolicyJetData.directWeight]; positivity
  have hchild : P.graphChild K L geometry.p Ψ ≤ M/w := by
    apply P.graphChild_le K L geometry.p geometry.ap Ψ (div_nonneg hM hw.le)
    intro row hrow
    apply (le_div_iff₀ hw).mpr
    simpa only [w,mul_comm] using hchildren row hrow
  have hweighted : w*P.graphChild K L geometry.p Ψ ≤ M := by
    simpa only [mul_comm] using (le_div_iff₀ hw).mp hchild
  have hcost := hcoeff P hLam hσP ((le_max_right _ _).trans hN) geometry.p
  have hchild0 : 0 ≤ P.graphChild K L geometry.p Ψ :=
    childJetStateMaximum_nonneg (m+1) K L 1 _ P.Q P.ρ _ P.N P.σ P.J P.i P.masks P.Z
      P.X P.Y (geometry.p-P.a) _ geometry.p P.t Ψ
  have hg := hgraph P hσP hJP hZP ((le_max_left _ _).trans hN) hi geometry
  calc
    _ ≤ P.graphCoefficient geometry.p*
        (((descriptorJetBound (m+3) K)^K)^2*((descriptorJetBound (m+3) K)^K)^2*
          P.graphChild K L geometry.p Ψ)+((2:ℝ)^P.N)^(-T) := hg
    _ = (P.graphCoefficient geometry.p*
        (((descriptorJetBound (m+3) K)^K)^2*((descriptorJetBound (m+3) K)^K)^2))*
          P.graphChild K L geometry.p Ψ+((2:ℝ)^P.N)^(-T) := by ring
    _ ≤ w*P.graphChild K L geometry.p Ψ+((2:ℝ)^P.N)^(-T) :=
      add_le_add (mul_le_mul_of_nonneg_right hcost hchild0) le_rfl
    _ ≤ _ := add_le_add hweighted le_rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_PolicyPrefixShell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual high-prefix shell reduces to retained-mask child states -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap
open PlanarFalconer (PolicyDescriptor policyDepth)

namespace PolicyJetData
variable {m : ℕ}

theorem directWeight_shift (P : PolicyJetData m) (p : ℕ) (lam σ ε δ : ℝ) :
    ((2:ℝ)^P.N)^δ*P.directWeight p lam σ ε = P.directWeight p lam σ (ε+δ) := by
  unfold directWeight
  rw [← Real.rpow_add (by positivity : 0 < (2:ℝ)^P.N)]
  congr 1
  ring

end PolicyJetData

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PolicyCommonBudgets
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One derivative budget for positive and angular policy steps -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap
open PlanarFalconer (policyDepth)

theorem exists_policy_prefix_common_budgets_oai
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {lam σ ε : ℝ} (hlam : 0 ≤ lam) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε)
    {J : ℕ} (hJ : 0 < J) (T δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W)
    (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ) (hφ : ∀ r, φ r = (Ψ r : ℂ))
    (hΨ : Measurable Ψ) (hpos : ∀ r, 0 ≤ Ψ r) (hzero : ∀ r ≤ 0, Ψ r = 0)
    (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
    {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) (minJet : ℕ := 0) :
    ∃ K : ℕ, minJet ≤ K ∧ ∀ minOrder : ℕ, ∃ (L : ℕ) (Z : ℝ) (N₀ : ℕ), minOrder ≤ L ∧ 1 ≤ Z ∧
      PolicyGraphBound m K L J lam σ (ε/2) (T+1+ε/2) Z N₀ Ψ ∧
      ∀ (P : PolicyJetData m) (hσP : P.σ = σ), P.lam = lam → P.J = J → P.Z = Z → N₀ ≤ P.N →
      P.i+1 ≤ P.J →
      (∀ b ∈ P.list, ∀ w : Sphere (m+3), ∃ c ∈ P.masks b,
        dist w c ≤ descriptorMaskRadius P.N P.σ b/2) →
      (∀ᵐ z ∂(P.ρ.restrict (P.Q.descendant P.X).carrier).prod
        (P.ρ.restrict (P.Q.descendant P.Y).carrier),
        δ ≤ dist z.1 z.2*(2:ℝ)^P.a ∧ dist z.1 z.2*(2:ℝ)^P.a ≤ W) →
      125*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side ≤
        ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ →
      ∀ (hleft : P.a₀ = P.a) (hwide : P.a+100*P.q < P.t₀)
        (hq : P.σ*(P.N:ℝ) ≤ P.q) (hhigh : (P.t₀:ℝ) ≤ P.t+P.σ*P.N),
      ∀ hprefix : 2*policyDepth P.policy P.N P.q P.a P.t₀ ≤ P.a+P.t₀,
      let geometry := P.prefixGeometry (by simpa only [hσP] using hσ)
        hleft hwide hq hhigh hprefix
      ∀ M : ℝ, 0 ≤ M →
      (∀ row, ∀ hrow : row ∈
        (P.Q.descendant P.X).occupiedPaths P.ρ (geometry.p-P.a) ×ˢ
          (P.Q.descendant P.Y).occupiedPaths P.ρ (geometry.p-P.a),
        P.directWeight geometry.p lam σ ε *
          (P.child geometry.p geometry.ap row hrow).envelope K L Ψ ≤ M) →
      ∀ w₀ : Sphere (m+3),
      (2:ℝ)^(-(P.a:ℝ))*
        (∫ r in Icc ((2:ℝ)^((P.t:ℝ)-1)) ((2:ℝ)^((P.t:ℝ)+1)),
          ‖charFun (maskedCellDistance w₀ P.Q P.ρ P.profile P.N P.σ P.J P.i P.a P.list
            P.masks (P.Q.descendant P.X) (P.Q.descendant P.Y)) r‖^2) ≤
      M+((2:ℝ)^P.N)^(-T) := by
  obtain ⟨K,hminJet,hconversion⟩ := exists_policy_scalar_conversion hgnomonic hquadratic m hσ hσ1
    (half_pos hε) lam (T+1) δ W hδ hW Ψ hΨ hpos hzero hone hV hΨV hsupp minJet
  refine ⟨K,hminJet,?_⟩
  intro minOrder
  obtain ⟨L,Z,Ng,hL,hZ,hgraph⟩ := exists_policy_graph_recurrence_at hgnomonic m K hlam hσ
    (half_pos hε) hJ (T+1+ε/2) φ Ψ hφ hΨ hpos hzero hV hΨV hsupp minOrder
  obtain ⟨Nc,hconvert⟩ := hconversion L Z (zero_lt_one.trans_le hZ)
  refine ⟨L,Z,max 1 (max Ng Nc),hL,hZ,?_,?_⟩
  · intro P hLam hσP hJP hZP hN
    exact hgraph P hLam hσP hJP hZP ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  · intro P hσP hLam hJP hZP hN hi hcover hsep hcenter hleft hwide hq hhigh hprefix
    let geometry := P.prefixGeometry (by simpa only [hσP] using hσ) hleft hwide hq hhigh hprefix
    dsimp only
    intro M hM hchildren w₀
    let c : ℝ := ((2:ℝ)^P.N)^(ε/2)
    have hc : 0 < c := by dsimp [c]; positivity
    have hinverse := policy_prefix_inverse_scales P (by simpa only [hσP] using hσ)
      hleft hwide hq hhigh
    have hs := hconvert P hσP hLam hZP
      ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
      hcover hsep hcenter hinverse.1 hinverse.2 w₀
    have hchild : ∀ row, ∀ hrow : row ∈
        (P.Q.descendant P.X).occupiedPaths P.ρ (geometry.p-P.a) ×ˢ
          (P.Q.descendant P.Y).occupiedPaths P.ρ (geometry.p-P.a),
        P.directWeight geometry.p lam σ (ε/2)*
          (P.child geometry.p geometry.ap row hrow).envelope K L Ψ ≤ M/c := by
      intro row hrow
      apply (le_div_iff₀ hc).mpr
      have he : c*P.directWeight geometry.p lam σ (ε/2) = P.directWeight geometry.p lam σ ε := by
        dsimp [c]
        rw [P.directWeight_shift]
        congr 1
        ring
      calc
        _ = (c*P.directWeight geometry.p lam σ (ε/2))*
            (P.child geometry.p geometry.ap row hrow).envelope K L Ψ := by ring
        _ ≤ M := by rw [he]; exact hchildren row hrow
    have hg := hgraph P hLam hσP hJP hZP
      ((le_max_left _ _).trans ((le_max_right _ _).trans hN)) hi geometry
      (M/c) (div_nonneg hM hc.le) hchild
    have hbase : 2 ≤ (2:ℝ)^P.N := le_self_pow₀ (by norm_num) (by
      have hh : 1 ≤ P.N := (le_max_left _ _).trans hN
      omega)
    have herr : c*((2:ℝ)^P.N)^(-(T+1+ε/2))+((2:ℝ)^P.N)^(-(T+1)) ≤
        ((2:ℝ)^P.N)^(-T) := by
      have hpower : c*((2:ℝ)^P.N)^(-(T+1+ε/2)) = ((2:ℝ)^P.N)^(-(T+1)) := by
        dsimp [c]
        rw [← Real.rpow_add (by positivity)]
        congr 1
        ring
      rw [hpower]
      have heq : ((2:ℝ)^P.N)^(-T) = (2:ℝ)^P.N*((2:ℝ)^P.N)^(-(T+1)) := by
        symm
        calc
          _ = (((2:ℝ)^P.N)^1)*((2:ℝ)^P.N)^(-(T+1)) := by rw [Real.rpow_one]
          _ = ((2:ℝ)^P.N)^(1+(-(T+1))) := (Real.rpow_add (by positivity) _ _).symm
          _ = _ := by congr 1; ring
      rw [heq]
      nlinarith [mul_le_mul_of_nonneg_right hbase
        (show 0 ≤ ((2:ℝ)^P.N)^(-(T+1)) by positivity)]
    calc
      _ ≤ c*P.envelope K L Ψ+((2:ℝ)^P.N)^(-(T+1)) := hs
      _ ≤ c*(M/c+((2:ℝ)^P.N)^(-(T+1+ε/2)))+((2:ℝ)^P.N)^(-(T+1)) := by gcongr
      _ = M+(c*((2:ℝ)^P.N)^(-(T+1+ε/2))+((2:ℝ)^P.N)^(-(T+1))) := by
        rw [mul_add,mul_div_cancel₀ _ hc.ne']
        ring
      _ ≤ _ := add_le_add le_rfl herr

end Falconer

end OAI
end

theorem solution : type_of% @OAI.Falconer.exists_policy_prefix_common_budgets_oai := @OAI.Falconer.exists_policy_prefix_common_budgets_oai
