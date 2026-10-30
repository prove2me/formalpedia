-- Prove2me | solution 1 for OAI.Falconer.exists_flexible_graph_child
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:17:51.805021+00:00
-- url     : https://prove2.me/submissions/d5df8879-07a1-4365-b132-041256aa15b1

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002
import Theorems.Thm_OAI_Falconer_exists_policy_recursion_bounds

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

theorem sourceAngularShellMeasure_real_mass_le (v : ℝ) (Ψ : ℝ → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ t, Ψ t ≤ B)
    (hs : ∀ t, 4 < t → Ψ t = 0) :
    (sourceAngularShellMeasure v Ψ).real univ ≤ 4*B := by
  apply (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (sourceAngularShellMeasure_mass_le v Ψ hB hb hs)).trans_eq
  exact ENNReal.toReal_ofReal (by positivity)

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

theorem endpoint_angular_terminal {d : ℕ} (a v : ℝ) (Ψ : ℝ → ℝ)
    {W B ℓ R : ℝ} (hW : 0 ≤ W) (hΨW : ∀ t, Ψ t ≤ W)
    (hΨsupport : ∀ t, 4 < t → Ψ t = 0) (hB : 0 ≤ B) (hR : 0 < R)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (M₁ M₂ : ℝ) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hm₁ : μ.real univ/M₁ ≤ R^ℓ) (hm₂ : ν.real univ/M₂ ≤ R^ℓ)
    (b c : Space d → Sphere d → ℂ)
    (hb : ∀ x w, ‖b x w‖ ≤ B) (hc : ∀ x w, ‖c x w‖ ≤ B) :
    independentAngularEnergy a v Ψ
      (fun z => endpointTransform μ M₁ b z.1 z.2)
      (fun z => endpointTransform ν M₂ c z.1 z.2) ≤
    (4*W*B^4*(sphereMeasure d).real univ^2)*
      (2:ℝ)^((d:ℝ)*(v-a))*R^(4*ℓ) := by
  let := PlanarFalconer.sourceAngularShellMeasure_finite v Ψ hW hΨW hΨsupport
  have hbound₁ (z : ℝ × Sphere d) : ‖endpointTransform μ M₁ b z.1 z.2‖ ≤ B*R^ℓ := by
    exact (endpointTransform_norm_le μ hM₁ b hb z.1 z.2).trans
      (by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hm₁ hB)
  have hbound₂ (z : ℝ × Sphere d) : ‖endpointTransform ν M₂ c z.1 z.2‖ ≤ B*R^ℓ := by
    exact (endpointTransform_norm_le ν hM₂ c hc z.1 z.2).trans
      (by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hm₂ hB)
  have h := independentAngularEnergy_bound a v Ψ _ _
    (mul_nonneg hB (Real.rpow_nonneg hR.le _))
    (mul_nonneg hB (Real.rpow_nonneg hR.le _)) hbound₁ hbound₂
  apply h.trans
  calc
    _ ≤ (2:ℝ)^((d:ℝ)*(v-a)) *
        ((B*R^ℓ)^2*(B*R^ℓ)^2*(sphereMeasure d).real univ^2)*(4*W) :=
      mul_le_mul_of_nonneg_left
        (PlanarFalconer.sourceAngularShellMeasure_real_mass_le v Ψ hW hΨW hΨsupport)
        (by positivity)
    _ = _ := by
      have hr : (R^ℓ)^4 = R^(4*ℓ) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hR.le]
        congr 1
        ring
      calc
        _ = (4*W*B^4*(sphereMeasure d).real univ^2)*
            (2:ℝ)^((d:ℝ)*(v-a))*(R^ℓ)^4 := by ring
        _ = _ := by rw [hr]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_Potential
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Finset

theorem finiteMin_le {ι : Type*} {s : Finset ι} (f : ι → ℝ)
    {i : ι} (hi : i ∈ s) : finiteMin s f ≤ f i := by
  rw [finiteMin, dite_eq_left ⟨i, hi⟩]
  exact Finset.inf'_le f hi

theorem le_finiteMin {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (f : ι → ℝ) {c : ℝ} (h : ∀ i ∈ s, c ≤ f i) : c ≤ finiteMin s f := by
  rw [finiteMin, dite_eq_left hs]
  exact Finset.le_inf' hs f h

theorem depthPairs_nonempty {a t Q : ℕ} (hQ : 0 < Q) (hw : a + Q ≤ t) :
    (depthPairs a t Q).Nonempty := by
  refine ⟨(a,a+Q), mem_depthPairs.mpr ?_⟩
  omega

theorem potential_le (A : ℕ → ℝ) {a t Q i j : ℕ}
    (hi : a ≤ i) (hij : i < j) (hjt : j ≤ t) (hgap : i + Q ≤ j) :
    potential A a t Q ≤ A i + A j :=
  finiteMin_le _ (mem_depthPairs.mpr ⟨hi,hij,hjt,hgap⟩)

theorem le_potential (A : ℕ → ℝ) {a t Q : ℕ} (hQ : 0 < Q)
    (hw : a+Q ≤ t) {c : ℝ}
    (h : ∀ i j, a ≤ i → i < j → j ≤ t → i+Q ≤ j → c ≤ A i + A j) :
    c ≤ potential A a t Q := by
  apply le_finiteMin (depthPairs_nonempty hQ hw)
  rintro ⟨i,j⟩ hij
  obtain ⟨hi, hij, hjt, hgap⟩ := mem_depthPairs.mp hij
  exact h i j hi hij hjt hgap

theorem potential_mono (A : ℕ → ℝ) {a b u t Q : ℕ}
    (hQ : 0 < Q) (hw : b+Q ≤ u) (hab : a ≤ b) (hut : u ≤ t) :
    potential A a t Q ≤ potential A b u Q := by
  apply le_potential A hQ hw
  intro i j hbi hij hju hgap
  exact potential_le A (hab.trans hbi) hij (hju.trans hut) hgap

theorem prefix_payment (A : ℕ → ℝ) {a p v t Q i₀ : ℕ}
    (hQ : 0 < Q) (hw : p+Q ≤ v) (hai : a ≤ i₀) (hip : i₀ ≤ p)
    (hvt : v ≤ t) (hcontrolled : ∀ i, p ≤ i → i+Q ≤ v → A p ≤ A i) :
    potential A a t Q + (A p - A i₀) ≤ potential A p v Q := by
  apply le_potential A hQ hw
  intro i j hpi hij hjv hgap
  have hparent := potential_le A hai (by omega : i₀ < j) (by omega : j ≤ t)
    (by omega : i₀+Q ≤ j)
  have hAi := hcontrolled i hpi (by omega)
  linarith

theorem suffix_payment (A : ℕ → ℝ) {a p t Q j₀ : ℕ}
    (hQ : 0 < Q) (hw : a+Q ≤ p) (hpj : p ≤ j₀) (hjt : j₀ ≤ t)
    (hcontrolled : ∀ j, a+Q ≤ j → j ≤ p → A p ≤ A j) :
    potential A a t Q + (A p - A j₀) ≤ potential A a p Q := by
  apply le_potential A hQ hw
  intro i j hai hij hjp hgap
  have hparent := potential_le A hai (by omega : i < j₀) hjt
    (by omega : i+Q ≤ j₀)
  have hAj := hcontrolled j (by omega) hjp
  linarith

theorem direct_origin_payment (A : ℕ → ℝ) {a p v b u l r L q Q i₀ : ℕ}
    (hq : 0 < q) (hQ : Q = 10*q) (hw : p+Q ≤ v)
    (hai : a ≤ i₀) (hip : i₀ ≤ p) (hlp : l ≤ p) (hpr : p ≤ r)
    (hl : l ≤ b+2*q) (hr : u ≤ r+2*q) (hLu : b+2*L ≤ u)
    (hv : v ≤ a+2*L) (hmin : A i₀ < A p)
    (hinner : ∀ n, l ≤ n → n ≤ r → A p ≤ A n) :
    potential A a v Q + (A p - A i₀) ≤ potential A p v Q := by
  have hi₀l : i₀ < l := by
    by_contra h
    have := hinner i₀ (by omega) (by omega)
    linarith
  apply prefix_payment A (by omega) hw hai hip (le_refl v)
  intro i hpi hiQ
  apply hinner i (by omega) (by omega)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_Ledger
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Finset

theorem intervalMin_attained (A : ℕ → ℝ) {a t : ℕ} (hat : a ≤ t) :
    ∃ i, a ≤ i ∧ i ≤ t ∧ intervalMin A a t = A i := by
  have hn : (Finset.Icc a t).Nonempty := ⟨a, Finset.mem_Icc.mpr ⟨le_rfl,hat⟩⟩
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_inf' hn A
  exact ⟨i,(Finset.mem_Icc.mp hi).1,(Finset.mem_Icc.mp hi).2,
    by simpa only [intervalMin, finiteMin, dite_eq_left hn] using he⟩

theorem intervalMin_le (A : ℕ → ℝ) {a t i : ℕ} (hai : a ≤ i) (hit : i ≤ t) :
    intervalMin A a t ≤ A i := finiteMin_le A (Finset.mem_Icc.mpr ⟨hai,hit⟩)

theorem height_nonneg (A : ℕ → ℝ) {a p : ℕ} (hap : a ≤ p) :
    0 ≤ height A a p := sub_nonneg.mpr (intervalMin_le A hap le_rfl)

theorem policy_prefix_payment (A : ℕ → ℝ) {a p v t l r q : ℕ}
    (hq : 0 < q) (hw : p+10*q ≤ v) (hap : a ≤ p) (hvt : v ≤ t)
    (hlp : l ≤ p) (htr : t ≤ r+2*q)
    (hinner : ∀ n, l ≤ n → n ≤ r → A p ≤ A n) :
    potential A a t (10*q) + height A a p ≤ potential A p v (10*q) := by
  obtain ⟨i,hai,hip,hmin⟩ := intervalMin_attained A hap
  unfold height
  rw [hmin]
  apply prefix_payment A (by omega) hw hai hip hvt
  intro n hpn hnv
  exact hinner n (by omega) (by omega)

theorem policy_suffix_payment (A : ℕ → ℝ) {a p t l r q : ℕ}
    (hq : 0 < q) (hw : a+10*q ≤ p) (hpt : p ≤ t)
    (hla : l ≤ a+2*q) (hpr : p ≤ r)
    (hinner : ∀ n, l ≤ n → n ≤ r → A p ≤ A n) :
    potential A a t (10*q) + (A p - intervalMin A p t) ≤
      potential A a p (10*q) := by
  obtain ⟨j,hpj,hjt,hmin⟩ := intervalMin_attained A hpt
  rw [hmin]
  apply suffix_payment A (by omega) hw hpj hjt
  intro n han hnp
  exact hinner n (by omega) (by omega)

theorem policy_direct_payment (A : ℕ → ℝ) {a p v b u l r L q : ℕ}
    (hq : 0 < q) (hw : p+10*q ≤ v) (hap : a ≤ p)
    (hlp : l ≤ p) (hpr : p ≤ r) (hl : l ≤ b+2*q) (hr : u ≤ r+2*q)
    (hLu : b+2*L ≤ u) (hv : v ≤ a+2*L)
    (hinner : ∀ n, l ≤ n → n ≤ r → A p ≤ A n) :
    potential A a v (10*q) + height A a p ≤ potential A p v (10*q) := by
  obtain ⟨i,hai,hip,hmin⟩ := intervalMin_attained A hap
  by_cases hcost : 0 < height A a p
  · have hi : A i < A p := by unfold height at hcost; rw [hmin] at hcost; linarith
    simpa only [height, hmin] using
      direct_origin_payment A hq rfl hw hai hip hlp hpr hl hr hLu hv hi hinner
  · have hz : height A a p = 0 := le_antisymm (not_lt.mp hcost) (height_nonneg A hap)
    rw [hz, add_zero]
    exact potential_mono A (by omega) hw hap le_rfl

theorem branch_cost_bound (V C : ℕ → ℝ) (n : ℕ)
    (hpay : ∀ k < n, V k + C k ≤ V (k+1)) :
    ∑ k ∈ Finset.range n, C k ≤ V n - V 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hs := ih (fun k hk => hpay k (by omega))
    have hn := hpay n (by omega)
    linarith

theorem profile_increments_telescope (A : ℕ → ℝ) (start : ℕ → ℕ) (n : ℕ) :
    ∑ k ∈ Finset.range n, -2 * (A (start (k+1)) - A (start k)) =
      2*A (start 0) - 2*A (start n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

theorem nearby_pair {a t f Q : ℕ} (hQ : 0 < Q) (hw : a+Q ≤ t)
    (haf : a ≤ f) (hft : f ≤ t) :
    ∃ i j, a ≤ i ∧ i < j ∧ j ≤ t ∧ i+Q = j ∧
      i ≤ f ∧ f ≤ j ∧ f ≤ i+Q ∧ j ≤ f+Q := by
  refine ⟨max a (f-Q), max a (f-Q)+Q, ?_⟩
  omega

theorem potential_near_final (A : ℕ → ℝ) {a t f Q : ℕ} {e : ℝ}
    (hQ : 0 < Q) (hw : a+Q ≤ t) (haf : a ≤ f) (hft : f ≤ t)
    (hlocal : ∀ i, a ≤ i → i ≤ t → i ≤ f+Q → f ≤ i+Q → A i ≤ A f+e) :
    potential A a t Q ≤ 2*A f+2*e := by
  obtain ⟨i,j,hai,hij,hjt,hgap,hif,hfj,hfi,hjf⟩ := nearby_pair hQ hw haf hft
  have hp := potential_le A (Q := Q) hai hij hjt (by omega)
  have hi := hlocal i hai (by omega) (by omega) hfi
  have hj := hlocal j (by omega) hjt hjf (by omega)
  linarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_InteriorPolicy
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem policy_right_block {N q a t : ℕ} (hq : 0 < q) (ht : t ≤ N) (hwide : a+100*q < t) :
    ∃ k ∈ policyBlocks N q a t, t-2*q ≤ (k+1)*q-1 := by
  let j := (t-q+1)/q
  have hj : 0 < j := Nat.div_pos (by omega) hq
  have hlo := Nat.div_mul_le_self (t-q+1) q
  have hhi := Nat.lt_mul_div_succ (t-q+1) hq
  change j*q ≤ t-q+1 at hlo
  rw [Nat.mul_comm q] at hhi
  change t-q+1 < (j+1)*q at hhi
  have hmul : (j+1)*q = j*q+q := by ring
  have he : (j-1+1)*q = j*q := by rw [Nat.sub_add_cancel hj]
  have he' : (j-1)*q+q = j*q := by simpa only [Nat.add_mul,one_mul] using he
  have hleft : a+q ≤ (j-1)*q := by omega
  have hkn : (j-1)*q ≤ N := by omega
  refine ⟨j-1,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,hleft,by omega⟩,by omega⟩
  exact Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le hq).mpr hkn)

theorem policyDepth_minimizes (A : ℕ → ℝ) {N q a t n : ℕ} (hq : 0 < q)
    (hne : (policyBlocks N q a t).Nonempty) (hn : n ≤ N)
    (hblock : n/q ∈ policyBlocks N q a t) : A (policyDepth A N q a t) ≤ A n := by
  have hkey := finiteArgmin_spec hne (fun k => A (policyRepresentative A N q k))
  have hcell : n ∈ policyBlock N q (n/q) := by
    apply Finset.mem_Ico.mpr
    have hlo := Nat.div_mul_le_self n q
    have hhi := Nat.lt_mul_div_succ n hq
    rw [Nat.mul_comm q] at hhi
    exact ⟨hlo,lt_min hhi (Nat.lt_succ_of_le hn)⟩
  exact (hkey.2 _ hblock).trans
    ((policyRepresentative_spec A hq ((Nat.div_mul_le_self n q).trans hn)).2.2.2 n hcell)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PolicyInteriorInterval
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem policy_blocks_order_convex {N q a t j k l : ℕ}
    (hj : j ∈ policyBlocks N q a t) (hl : l ∈ policyBlocks N q a t)
    (hjk : j ≤ k) (hkl : k ≤ l) : k ∈ policyBlocks N q a t := by
  have hj' := policyBlocks_mem hj
  have hl' := policyBlocks_mem hl
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),?_,?_⟩
  · exact hj'.2.1.trans (Nat.mul_le_mul_right q hjk)
  · exact (Nat.mul_le_mul_right q (Nat.add_le_add_right hkl 1)).trans hl'.2.2

theorem policy_interior_interval (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q)
    (ht : t ≤ N) (hwide : a+100*q < t) :
    ∃ l u : ℕ, l ≤ a+2*q ∧ t ≤ u+2*q ∧
      l ≤ policyDepth A N q a t ∧ policyDepth A N q a t ≤ u ∧
      ∀ n, l ≤ n → n ≤ u → A (policyDepth A N q a t) ≤ A n := by
  let S := policyBlocks N q a t
  have hS : S.Nonempty := policyBlocks_nonempty hq ht hwide
  let j := S.min' hS
  let k := S.max' hS
  have hj : j ∈ S := S.min'_mem hS
  have hk : k ∈ S := S.max'_mem hS
  have hj' := policyBlocks_mem hj
  have hk' := policyBlocks_mem hk
  have hkpos : 0 < (k+1)*q := Nat.mul_pos (by omega) hq
  have huN : (k+1)*q-1 ≤ N := by omega
  obtain ⟨j₀,hj₀,hleft⟩ := policy_left_block hq ht hwide
  obtain ⟨k₀,hk₀,hright⟩ := policy_right_block hq ht hwide
  have hjj₀ : j ≤ j₀ := S.min'_le j₀ hj₀
  have hk₀k : k₀ ≤ k := S.le_max' k₀ hk₀
  have hlower : j*q ≤ a+2*q := (Nat.mul_le_mul_right q hjj₀).trans hleft
  have hupper : t ≤ ((k+1)*q-1)+2*q := by
    have hh := Nat.mul_le_mul_right q (Nat.add_le_add_right hk₀k 1)
    omega
  let key := policyKey A N q a t
  have hkey : key ∈ S := (finiteArgmin_spec hS (fun j => A (policyRepresentative A N q j))).1
  have hkeylo : j ≤ key := S.min'_le key hkey
  have hkeyhi : key ≤ k := S.le_max' key hkey
  have hrep := policyRepresentative_spec A hq
    ((Nat.le_div_iff_mul_le hq).mp (policyBlocks_mem hkey).1)
  have hplo : j*q ≤ policyDepth A N q a t := (Nat.mul_le_mul_right q hkeylo).trans hrep.1
  have hphi : policyDepth A N q a t ≤ (k+1)*q-1 := by
    have hh := hrep.2.1.trans_le (Nat.mul_le_mul_right q (Nat.add_le_add_right hkeyhi 1))
    exact Nat.le_sub_one_of_lt hh
  refine ⟨j*q,(k+1)*q-1,hlower,hupper,hplo,hphi,?_⟩
  intro n hnlo hnhi
  have hnN : n ≤ N := hnhi.trans huN
  have hjn : j ≤ n/q := (Nat.le_div_iff_mul_le hq).mpr hnlo
  have hnk : n/q ≤ k := by
    have hh : n < (k+1)*q := by omega
    have hd := (Nat.div_lt_iff_lt_mul hq).mpr hh
    omega
  exact policyDepth_minimizes A hq hS hnN (policy_blocks_order_convex hj hk hjn hnk)

theorem policy_representatives_card (A : ℕ → ℝ) (N q : ℕ) :
    (policyRepresentatives A N q).card ≤ N/q+1 :=
  Finset.card_image_le.trans (by simp)

theorem policyDepth_mem_representatives (A : ℕ → ℝ) {N q a t : ℕ}
    (hne : (policyBlocks N q a t).Nonempty) :
    policyDepth A N q a t ∈ policyRepresentatives A N q := by
  have hk := (finiteArgmin_spec hne (fun k => A (policyRepresentative A N q k))).1
  exact Finset.mem_image.mpr ⟨policyKey A N q a t,(Finset.mem_filter.mp hk).1,rfl⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PolicyDescriptors
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem policyDescriptor_anchor_mem (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q)
    {d : PolicyDescriptor} (hd : d ∈ policyDescriptorList A N q a t) :
    descriptorAnchor d ∈ policyRepresentatives A N q := by
  obtain ⟨z,hz,hd⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨hz,_,_,hwide⟩ := Finset.mem_filter.mp hz
  have huN : z.2 ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hz).2)
  rw [originDescriptor_anchor A hd]
  exact policyDepth_mem_representatives A (policyBlocks_nonempty hq huN hwide)

end PlanarFalconer

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
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SuffixGrouping
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarse grouping of the actual all-dimensional distance cells

Two fine distance distributions sharing one bin force all distances of
their full cell pairs into a common coarse collision band. The width
constant retains the ambient dimension explicitly.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem cellDistance_mass (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (P Q : DyadicCube d) : cellDistance μ ν P Q univ = μ P.carrier*ν Q.carrier := by
  rw [cellDistance,Measure.map_apply (by fun_prop) MeasurableSet.univ,preimage_univ,
    ← univ_prod_univ,Measure.prod_prod,Measure.restrict_apply_univ,Measure.restrict_apply_univ]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RetainedPairs
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact decomposition into the suffix cells having a witness

Only actual original-law restrictions occur. Empty intersections with the
parent's good-pair set contribute zero, so retaining witnessed cells is an
exact identity, before their full cell measures are used for comparison.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

theorem testedCellDistance_le (μ ν : Measure (Space d))
    (P Q : DyadicCube d) (G : Set (Space d × Space d)) :
    testedCellDistance μ ν P Q G ≤ cellDistance μ ν P Q := by
  exact Measure.map_mono Measure.restrict_le_self (by fun_prop)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularizedCellCounts
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual descendant counts for a single regularized profile -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem RegularizedProfileData.cell_mass_upper {Q : DyadicCube d}
    {ρ : Measure (Space d)} {N : ℕ} {s lam : ℝ} {m : ℝ → ℝ}
    (h : RegularizedProfileData Q ρ N s lam m)
    {a : ℕ} (ha : a ≤ N) (X : CellPath d) (hX : X.length = a) :
    (ρ (Q.descendant X).carrier).toReal ≤
      ((2:ℝ)^N)^(((d:ℝ)+1)*lam-m ((a:ℝ)/N)) := by
  by_cases hp : 0 < ρ (Q.descendant X).carrier
  · exact (h.cells a ha X hX hp).2.trans_eq
      (Real.rpow_add (by positivity) _ _).symm
  · have hz : ρ (Q.descendant X).carrier = 0 := le_antisymm (le_of_not_gt hp) bot_le
    rw [hz,ENNReal.toReal_zero]
    positivity

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileNear
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized near reduction for the actual regularized profile

The child energies retain the original endpoint symbols. No separation of
the parent cells is imposed; the near relation is on their two internal
center displacements, as in the manuscript.
-/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem profile_angular_terminal (Q : DyadicCube d) (ρ : Measure (Space d))
    {m : ℝ → ℝ} {N : ℕ} {s lam : ℝ}
    (hreg : Regularization.RegularizedProfileData Q ρ N s lam m) (hN : 0 < N)
    {a q : ℕ} (ha : a ≤ N) (X Y : List (Fin d → Bool))
    (hX : X.length = a) (hY : Y.length = a) (v : ℝ)
    (hv : v ≤ (a:ℝ)+100*q) (Ψ : ℝ → ℝ) {W B : ℝ}
    (hW : 0 ≤ W) (hΨ : ∀ t, Ψ t ≤ W) (hsupp : ∀ t, 4 < t → Ψ t = 0)
    (hB : 0 ≤ B) (b c : Space d → Sphere d → ℂ)
    (hb : ∀ x w, ‖b x w‖ ≤ B) (hc : ∀ x w, ‖c x w‖ ≤ B) :
    independentAngularEnergy a v Ψ
      (fun z => endpointTransform (ρ.restrict (Q.descendant X).carrier)
        (profileModelMass m N a) b z.1 z.2)
      (fun z => endpointTransform (ρ.restrict (Q.descendant Y).carrier)
        (profileModelMass m N a) c z.1 z.2) ≤
    (4*W*B^4*(sphereMeasure d).real univ^2) *
      ((2:ℝ)^N)^(100*(d:ℝ)*q/N+4*((d:ℝ)+1)*lam) := by
  let := hreg.probability
  have hR : 0 < (2:ℝ)^N := by positivity
  have hM : 0 < profileModelMass m N a := by unfold profileModelMass; positivity
  have hm (Z : List (Fin d → Bool)) (hZ : Z.length = a) :
      (ρ.restrict (Q.descendant Z).carrier).real univ/profileModelMass m N a ≤
        ((2:ℝ)^N)^(((d:ℝ)+1)*lam) := by
    rw [measureReal_def,Measure.restrict_apply_univ]
    apply (div_le_iff₀ hM).mpr
    exact (hreg.cell_mass_upper ha Z hZ).trans_eq
      (by rw [profileModelMass,← Real.rpow_add hR]; rfl)
  have h := endpoint_angular_terminal (a:ℝ) v Ψ hW hΨ hsupp hB hR
    (ρ.restrict (Q.descendant X).carrier) (ρ.restrict (Q.descendant Y).carrier)
    (profileModelMass m N a) (profileModelMass m N a) hM hM
    (hm X hX) (hm Y hY) b c hb hc
  have hwidth : (2:ℝ)^((d:ℝ)*(v-a)) ≤
      ((2:ℝ)^N)^(100*(d:ℝ)*q/N) := by
    rw [dyadic_rpow_change_base hN]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  apply h.trans
  calc
    _ ≤ (4*W*B^4*(sphereMeasure d).real univ^2) *
        ((2:ℝ)^N)^(100*(d:ℝ)*q/N) * ((2:ℝ)^N)^(4*(((d:ℝ)+1)*lam)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwidth (by positivity))
        (by positivity)
    _ = _ := by rw [mul_assoc,← Real.rpow_add hR]; congr 2; ring

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
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ActualFarBuffer
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem uniform_source_far_buffer {sig : ℝ} (hsig : 0 < sig) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L v a : ℕ,
      let L₀ := sourceFarBuffer N L sig
      let h := v-2*L₀
      a < h →
      let d := h-a
      a+d = h ∧ a+d+5 < v ∧
      (v:ℝ)-(a+d:ℕ) = 2*(L₀:ℝ) ∧ (L:ℝ) ≤ (L₀:ℝ) ∧
      10*sig*(N:ℝ) ≤ (L₀:ℝ) := by
  obtain ⟨N₀,h₀⟩ := exists_nat_gt (1/sig)
  refine ⟨N₀,?_⟩
  intro N hN L v a
  dsimp only
  intro hah
  have hNs : 1/sig < (N:ℝ) := h₀.trans_le (Nat.cast_le.mpr hN)
  have hsigN : 1 < sig*(N:ℝ) := by
    have ht := (div_lt_iff₀ hsig).mp hNs
    linarith
  have hslack := sourceFarBuffer_ge_slack N L sig
  have hbuf : 5 < 2*sourceFarBuffer N L sig := by
    have hb : (5:ℝ) < 2*(sourceFarBuffer N L sig:ℝ) := by linarith
    exact_mod_cast hb
  have h2 : 2*sourceFarBuffer N L sig ≤ v := by omega
  have he : a+(v-2*sourceFarBuffer N L sig-a) = v-2*sourceFarBuffer N L sig := by omega
  refine ⟨he,by omega,?_,Nat.cast_le.mpr (sourceFarBuffer_ge_length N L sig),hslack⟩
  rw [he,Nat.cast_sub h2,Nat.cast_mul,Nat.cast_ofNat]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PrefixPolicyGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem source_policy_block_lower (N : ℕ) (kap : ℝ) :
    kap*(N:ℝ) ≤ (sourcePolicyBlock N kap:ℝ) := Nat.le_ceil _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ActualDirectBuffer
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem uniform_source_ceiling_slack {sig kap : ℝ}
    (hsig : 0 < sig) (hgap : sig < kap/1000) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀,
      ⌈10*sig*(N:ℝ)⌉₊ < sourcePolicyBlock N kap ∧
      10*sig*(N:ℝ) ≤ (sourcePolicyBlock N kap:ℝ) ∧
      sig*(N:ℝ) ≤ (sourcePolicyBlock N kap:ℝ) := by
  obtain ⟨N₀,h₀⟩ := exists_nat_gt (1/sig)
  refine ⟨max 1 N₀,by omega,?_⟩
  intro N hN
  have hNs : 1/sig < (N:ℝ) := h₀.trans_le (Nat.cast_le.mpr (by omega))
  have hsigN : 1 < sig*(N:ℝ) := by
    have := (div_lt_iff₀ hsig).mp hNs
    linarith
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 10*sig*(N:ℝ) by positivity)
  have hblock := source_policy_block_lower N kap
  have hgapN : 1000*sig*(N:ℝ) ≤ kap*N :=
    mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  have hlt : (⌈10*sig*(N:ℝ)⌉₊:ℝ) < (sourcePolicyBlock N kap:ℝ) := by linarith
  exact ⟨Nat.cast_lt.mp hlt,by linarith,by linarith⟩

theorem direct_buffer_eq_length {N L q a v : ℕ} {sig : ℝ}
    (hceil : ⌈10*sig*(N:ℝ)⌉₊ < q) (hw : a+100*q < v)
    (hdirect : v-2*sourceFarBuffer N L sig ≤ a) :
    sourceFarBuffer N L sig = L ∧ v ≤ a+2*L ∧ 0 < L := by
  have hv : v ≤ a+2*sourceFarBuffer N L sig := by omega
  have hL : ⌈10*sig*(N:ℝ)⌉₊ ≤ L := by
    by_contra h
    have he : sourceFarBuffer N L sig = ⌈10*sig*(N:ℝ)⌉₊ := max_eq_right (by omega)
    rw [he] at hv
    omega
  have he : sourceFarBuffer N L sig = L := max_eq_left hL
  rw [he] at hv
  exact ⟨he,hv,by omega⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ActualPolicyPayments
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem actual_prefix_policy_payment (A : ℕ → ℝ) {N q a t v : ℕ}
    (hq : 0 < q) (htN : t ≤ N) (hw : a+100*q < t)
    (hpref : 2*policyDepth A N q a t ≤ a+t) (hvt : v ≤ t) (hhigh : t-v ≤ q) :
    let p := policyDepth A N q a t
    p+10*q ≤ v ∧
      potential A a t (10*q)+height A a p ≤ potential A p v (10*q) := by
  have hg := prefix_policy_geometry A hq htN hw hpref
  obtain ⟨l,r,hl,hr,hlp,hpr,hinner⟩ := policy_interior_interval A hq htN hw
  have hwidth : policyDepth A N q a t+10*q ≤ v := by omega
  exact ⟨hwidth,policy_prefix_payment A hq hwidth hg.1.le hvt hlp hr hinner⟩

theorem actual_suffix_policy_payment (A : ℕ → ℝ) {N q a t : ℕ}
    (hq : 0 < q) (htN : t ≤ N) (hw : a+100*q < t)
    (hsuffix : a+t < 2*policyDepth A N q a t) :
    let p := policyDepth A N q a t
    a+10*q ≤ p ∧
      potential A a t (10*q)+(A p-intervalMin A p t) ≤ potential A a p (10*q) := by
  have hp := policyDepth_interior A hq (policyBlocks_nonempty hq htN hw)
  obtain ⟨l,r,hl,hr,hlp,hpr,hinner⟩ := policy_interior_interval A hq htN hw
  have hwidth : a+10*q ≤ policyDepth A N q a t := by omega
  exact ⟨hwidth,policy_suffix_payment A hq hwidth (by omega) hl hpr hinner⟩

theorem actual_direct_policy_payment (A : ℕ → ℝ) {N q a v a₀ t₀ : ℕ}
    (hq : 0 < q) (hw : a+100*q < v) {d : PolicyDescriptor}
    (hd : d ∈ policyDescriptorList A N q a₀ t₀)
    (hap : a < descriptorAnchor d)
    (hdirect : v ≤ a+2*descriptorLength d)
    (hscale : 2*descriptorAnchor d ≤ a+v+2*q) :
    descriptorAnchor d+10*q ≤ v ∧
      potential A a v (10*q)+height A a (descriptorAnchor d) ≤
        potential A (descriptorAnchor d) v (10*q) := by
  obtain ⟨z,hz,hd⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨hz,_,_,hzwide⟩ := Finset.mem_filter.mp hz
  have huN : z.2 ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hz).2)
  have hp := originDescriptor_anchor A hd
  have hlength := originDescriptor_length A hq huN hzwide hd
  have hlengthp := originDescriptor_length_le_anchor A hd
  obtain ⟨l,r,hl,hr,hlp,hpr,hinner⟩ := policy_interior_interval A hq huN hzwide
  rw [← hp] at hlp hpr hinner
  have hwidth : descriptorAnchor d+10*q ≤ v := by omega
  refine ⟨hwidth,policy_direct_payment A hq hwidth hap.le hlp hpr hl hr ?_ hdirect hinner⟩
  omega

end PlanarFalconer

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

 theorem reached_anchor_strictly_reduces_list (A : ℕ → ℝ) (N q a₀ t₀ : ℕ) {a p : ℕ}
    (hap : a ≤ p) {d : PolicyDescriptor}
    (hd : d ∈ remainingPolicyDescriptors A N q a₀ t₀ a) (hp : descriptorAnchor d ≤ p) :
    (remainingPolicyDescriptors A N q a₀ t₀ p).card <
      (remainingPolicyDescriptors A N q a₀ t₀ a).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨remainingPolicyDescriptors_mono A N q a₀ t₀ hap,?_⟩
  intro he
  rw [← he] at hd
  have hh := (Finset.mem_filter.mp hd).2
  omega

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_DirectPolicyWitness
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem remaining_descriptor_companion (A : ℕ → ℝ) {N q a₀ t₀ a : ℕ}
    (hq : 0 < q) {d : PolicyDescriptor}
    (hd : d ∈ remainingPolicyDescriptors A N q a₀ t₀ a) :
    PolicyDescriptor.parallel (max a (descriptorAnchor d-descriptorLength d))
      (descriptorAnchor d) ∈ remainingPolicyDescriptors A N q a₀ t₀ a := by
  classical
  obtain ⟨hd,hap⟩ := Finset.mem_filter.mp hd
  obtain ⟨z,hz,hd⟩ := Finset.mem_biUnion.mp hd
  have hz' := Finset.mem_filter.mp hz
  have huN : z.2 ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hz'.1).2)
  have hp := originDescriptor_anchor A hd
  have hl := originDescriptor_length A hq huN hz'.2.2.2 hd
  have hLp := originDescriptor_length_le_anchor A hd
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_biUnion.mpr ⟨z,hz,?_⟩,hap⟩
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  refine ⟨max a (descriptorAnchor d-descriptorLength d),Finset.mem_Ico.mpr ⟨?_,?_⟩,?_⟩
  · rw [← hp]
    omega
  · omega
  · rw [hp]

theorem actual_direct_policy_witness (A : ℕ → ℝ) {N q a₀ t₀ a v : ℕ} {sig : ℝ}
    (hsig : 0 ≤ sig) (hq : 0 < q) (hceil : ⌈10*sig*(N:ℝ)⌉₊ < q)
    (hslack : sig*(N:ℝ) ≤ (q:ℝ)) (hslack10 : 10*sig*(N:ℝ) ≤ (q:ℝ))
    (ht : (t₀:ℝ) ≤ (v:ℝ)+sig*N) (hw : a+100*q < v)
    (hdirect : v-2*sourceFarBuffer N
      ((remainingPolicyDescriptors A N q a₀ t₀ a).sup descriptorLength) sig ≤ a) :
    ∃ d : PolicyDescriptor, DirectPolicyWitness A N q a₀ t₀ a v sig d := by
  classical
  let S := remainingPolicyDescriptors A N q a₀ t₀ a
  have hb := direct_buffer_eq_length hceil hw hdirect
  have hS : S.Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    have hz : S.sup descriptorLength = 0 := by rw [he]; rfl
    exact (Nat.ne_of_gt hb.2.2) hz
  obtain ⟨d,hd,hmax⟩ := Finset.exists_mem_eq_sup S hS descriptorLength
  dsimp only [S] at hmax
  have hmax' := hmax.symm
  have hdir : v ≤ a+2*descriptorLength d := by simpa only [hmax] using hb.2.1
  have hmem := Finset.mem_filter.mp hd
  have hap : a < descriptorAnchor d := hmem.2
  obtain ⟨z,hz,hzd⟩ := Finset.mem_biUnion.mp hmem.1
  have hz' := Finset.mem_filter.mp hz
  have huN : z.2 ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hz'.1).2)
  have hl := originDescriptor_length A hq huN hz'.2.2.2 hzd
  have hLp := originDescriptor_length_le_anchor A hzd
  have hpt : descriptorAnchor d+descriptorLength d ≤ t₀ := hl.2.2.trans hz'.2.2.1
  have hptR : (descriptorAnchor d:ℝ)+(descriptorLength d:ℝ) ≤ (t₀:ℝ) := by exact_mod_cast hpt
  have hsigN : 0 ≤ sig*(N:ℝ) := mul_nonneg hsig (Nat.cast_nonneg _)
  have hdirR : (v:ℝ) ≤ (a:ℝ)+2*(descriptorLength d:ℝ) := by exact_mod_cast hdir
  have hmidR : 2*(descriptorAnchor d:ℝ) ≤ (a:ℝ)+v+2*q := by linarith
  have hmid : 2*descriptorAnchor d ≤ a+v+2*q := by exact_mod_cast hmidR
  have hwidth : descriptorAnchor d+10*q ≤ v := by omega
  have hwidthR : (descriptorAnchor d:ℝ)+10*(q:ℝ) ≤ (v:ℝ) := by exact_mod_cast hwidth
  have hn : ((descriptorAnchor d-a:ℕ):ℝ) = (descriptorAnchor d:ℝ)-a := Nat.cast_sub hap.le
  have hgs : ((descriptorAnchor d-descriptorLength d:ℕ):ℝ) =
      (descriptorAnchor d:ℝ)-descriptorLength d := Nat.cast_sub hLp
  refine ⟨d, {
    mem := hd
    maximal := hmax'
    buffer := ?_
    direct_depth := hdir
    anchor_gt := hap
    anchor_lt := by omega
    width := hwidth
    companion := remaining_descriptor_companion A hq hd
    g_lt := by omega
    g_slack := ?_
    frequency_slack := by linarith
    depth_scale := ?_
    length_scale := ?_
    midpoint := hmid
    shrinks := reached_anchor_strictly_reduces_list A N q a₀ t₀ hap.le hd le_rfl
    payment := (actual_direct_policy_payment A hq hw hmem.1 hap hdir hmid).2 }⟩
  · simpa only [← hmax] using hb.1
  · rw [Nat.cast_max,hgs,sub_le_iff_le_add]
    apply max_le <;> linarith [show 0 ≤ sig*(N:ℝ) by positivity]
  · rw [hn]
    linarith
  · have haR : (a:ℝ) < (descriptorAnchor d:ℝ) := Nat.cast_lt.mpr hap
    linarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularNearProgress
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem remaining_maximum_preserved (A : ℕ → ℝ) {N q a₀ t₀ a p : ℕ}
    (hap : a ≤ p) {d : PolicyDescriptor}
    (hd : d ∈ remainingPolicyDescriptors A N q a₀ t₀ a)
    (hm : descriptorLength d = (remainingPolicyDescriptors A N q a₀ t₀ a).sup descriptorLength)
    (hanchor : p < descriptorAnchor d) :
    (remainingPolicyDescriptors A N q a₀ t₀ p).sup descriptorLength =
      (remainingPolicyDescriptors A N q a₀ t₀ a).sup descriptorLength := by
  apply le_antisymm
  · exact Finset.sup_mono (remainingPolicyDescriptors_mono A N q a₀ t₀ hap)
  · rw [← hm]
    exact Finset.le_sup (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hd).1,hanchor⟩)

theorem actual_near_progress (A : ℕ → ℝ) {N q a₀ t₀ a v : ℕ} {sig : ℝ}
    (hq : 0 < q) (hceil : ⌈10*sig*(N:ℝ)⌉₊ < q)
    (hnear : a < v-2*sourceFarBuffer N
      ((remainingPolicyDescriptors A N q a₀ t₀ a).sup descriptorLength) sig) :
    let S := remainingPolicyDescriptors A N q a₀ t₀ a
    let L := S.sup descriptorLength
    let b := v-2*sourceFarBuffer N L sig
    v ≤ b+100*q ∨
      (∃ d ∈ S, descriptorLength d = L ∧ a < descriptorAnchor d ∧ descriptorAnchor d ≤ b ∧
        descriptorAnchor d ∈ policyRepresentatives A N q ∧
        (remainingPolicyDescriptors A N q a₀ t₀ b).card < S.card) ∨
      ((remainingPolicyDescriptors A N q a₀ t₀ b).sup descriptorLength = L ∧
        v-2*sourceFarBuffer N
          ((remainingPolicyDescriptors A N q a₀ t₀ b).sup descriptorLength) sig = b) := by
  classical
  dsimp only
  let S := remainingPolicyDescriptors A N q a₀ t₀ a
  let L := S.sup descriptorLength
  let b := v-2*sourceFarBuffer N L sig
  by_cases hterm : v ≤ b+100*q
  · exact Or.inl hterm
  apply Or.inr
  have hb := direct_buffer_eq_length hceil (by omega : b+100*q < v) (le_refl b)
  have hLpos : 0 < L := hb.2.2
  have hS : S.Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    have hz : L = 0 := by simp [L,he]
    omega
  by_cases hpassed : ∃ d ∈ S, descriptorLength d = L ∧ descriptorAnchor d ≤ b
  · obtain ⟨d,hd,hm,hdb⟩ := hpassed
    have hap := (Finset.mem_filter.mp hd).2
    exact Or.inl ⟨d,hd,hm,hap,hdb,
      policyDescriptor_anchor_mem A hq (Finset.mem_filter.mp hd).1,
      reached_anchor_strictly_reduces_list A N q a₀ t₀ hnear.le hd hdb⟩
  · obtain ⟨d,hd,hm⟩ := Finset.exists_mem_eq_sup S hS descriptorLength
    have hdb : b < descriptorAnchor d := by
      by_contra h
      exact hpassed ⟨d,hd,hm.symm,by omega⟩
    have he := remaining_maximum_preserved A hnear.le hd hm.symm hdb
    exact Or.inr ⟨he,by rw [he]⟩

end PlanarFalconer

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

 theorem value_measurable (f : DescriptorJetSymbol n K L F D)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ)
    (S : PolicyDescriptor → Finset (Sphere (n+2))) (A : ℝ) :
    Measurable (Function.uncurry (f.value Q ρ m N σ J i S A)) := by
  have hp := descriptorJetProduct_measurable Q ρ m N σ J i F id S
    (fun b => (f.jet b).order) (fun b _ => (f.jet b).vectors) (fun _ _ => measurable_const)
  exact hp.mul (f.multiplier_measurable A)

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

end DescriptorJetSymbol
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_PositiveSuffix
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual policy suffix transition for positive distance counts -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor descriptorAnchor descriptorLength)
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

theorem positiveCollisionCount_ne_top (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ) (A : ℕ → ℝ)
    (N : ℕ) (σ : ℝ) (J i q a t : ℕ) (X Y : List (Fin d → Bool)) :
    positiveCollisionCount w₀ Q ρ m A N σ J i q a t X Y ≠ ⊤ := by
  unfold positiveCollisionCount
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_PositiveTerminal
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Terminal bounds for the actual positive distance states

The profile is evaluated at integer depths in the recursive state.  The
regularized class stores its profile on [0,1], so the final theorem explicitly
uses `u ↦ m (u / N)` when passing to that state.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem testedCellDistance_mass_le (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (P Q : DyadicCube d) (G : Set (Space d × Space d)) :
    testedCellDistance ρ ρ P Q G univ ≤ ρ P.carrier * ρ Q.carrier := by
  exact (testedCellDistance_le ρ ρ P Q G univ).trans_eq (cellDistance_mass ρ ρ P Q)

theorem positiveCollisionCount_mass_bound (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ) (A : ℕ → ℝ)
    (N : ℕ) (σ : ℝ) (J i q a t : ℕ) (X Y : List (Fin d → Bool))
    (ℓ : ℝ)
    (hX : ρ (Q.descendant X).carrier ≤ ENNReal.ofReal (((2:ℝ)^N)^(ℓ-m a)))
    (hY : ρ (Q.descendant Y).carrier ≤ ENNReal.ofReal (((2:ℝ)^N)^(ℓ-m a))) :
    positiveCollisionCount w₀ Q ρ m A N σ J i q a t X Y ≤
      ENNReal.ofReal ((2:ℝ)^(t-a)*((2:ℝ)^N)^(4*ℓ)) := by
  let θ := testedCellDistance ρ ρ (Q.descendant X) (Q.descendant Y)
    (policyTestPairs w₀ Q ρ m A N σ J i q a t)
  have ht : θ univ ≤ (ENNReal.ofReal (((2:ℝ)^N)^(ℓ-m a)))^2 := by
    exact (testedCellDistance_mass_le ρ _ _ _).trans
      (by simpa only [pow_two] using mul_le_mul' hX hY)
  have hc : (θ.prod θ) {z : ℝ × ℝ | |z.1-z.2| ≤ 100*((d:ℝ)+1)/(2:ℝ)^t} ≤
      (ENNReal.ofReal (((2:ℝ)^N)^(ℓ-m a)))^4 := by
    calc
      _ ≤ (θ.prod θ) univ := measure_mono (subset_univ _)
      _ = θ univ * θ univ := by rw [← univ_prod_univ,Measure.prod_prod]
      _ ≤ _ := by convert mul_le_mul' ht ht using 1 <;> first | (with_reducible_and_instances rfl) | ring
  change ENNReal.ofReal ((2:ℝ)^(t-a)*((2:ℝ)^N)^(4*m a)) * (θ.prod θ) _ ≤ _
  apply (mul_le_mul' le_rfl hc).trans_eq
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hp : ((((2:ℝ)^N)^(ℓ-m a))^4) = ((2:ℝ)^N)^(4*(ℓ-m a)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity)]
    congr 1
    ring
  rw [hp,mul_assoc,← Real.rpow_add (by positivity)]
  congr 2
  ring

theorem positiveCollisionCount_regularized (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) {m : ℝ → ℝ} {N : ℕ} {s lam : ℝ}
    (hreg : Regularization.RegularizedProfileData Q ρ N s lam m)
    (A : ℕ → ℝ) (σ : ℝ) (J i q : ℕ) {a t : ℕ}
    (ha : a ≤ N) (X Y : List (Fin d → Bool))
    (hX : X.length = a) (hY : Y.length = a) :
    positiveCollisionCount w₀ Q ρ (fun u => m (u/N)) A N σ J i q a t X Y ≤
      ENNReal.ofReal ((2:ℝ)^(t-a)*((2:ℝ)^N)^(4*((d:ℝ)+1)*lam)) := by
  let := hreg.probability
  have hcell (P : List (Fin d → Bool)) (hP : P.length = a) :
      ρ (Q.descendant P).carrier ≤
        ENNReal.ofReal (((2:ℝ)^N)^(((d:ℝ)+1)*lam-m ((a:ℝ)/N))) := by
    by_cases hp : 0 < ρ (Q.descendant P).carrier
    · rw [← ENNReal.ofReal_toReal (measure_ne_top ρ _)]
      apply ENNReal.ofReal_le_ofReal
      exact (hreg.cells a ha P hP hp).2.trans_eq
        (Real.rpow_add (by positivity) _ _).symm
    · simp only [not_lt,le_zero_iff] at hp
      rw [hp]
      exact zero_le
  simpa only [mul_assoc] using positiveCollisionCount_mass_bound w₀ Q ρ
    (fun u => m (u/N)) A N σ J i q a t X Y (((d:ℝ)+1)*lam)
    (hcell X hX) (hcell Y hY)

theorem positiveCollisionCount_terminal (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) {m : ℝ → ℝ} {N : ℕ} {s lam : ℝ}
    (hreg : Regularization.RegularizedProfileData Q ρ N s lam m)
    (hN : 0 < N) (A : ℕ → ℝ) (σ : ℝ) (J i q : ℕ) {a t : ℕ}
    (ha : a ≤ N) (hat : a ≤ t) (ht : t ≤ a+100*q)
    (X Y : List (Fin d → Bool)) (hX : X.length = a) (hY : Y.length = a) :
    positiveCollisionCount w₀ Q ρ (fun u => m (u/N)) A N σ J i q a t X Y ≤
      ENNReal.ofReal (((2:ℝ)^N)^(100*(q:ℝ)/N+4*((d:ℝ)+1)*lam)) := by
  let := hreg.probability
  apply (positiveCollisionCount_regularized w₀ Q ρ hreg A σ J i q ha X Y hX hY).trans
  apply ENNReal.ofReal_le_ofReal
  have hwidth : (2:ℝ)^(t-a) ≤ ((2:ℝ)^N)^(100*(q:ℝ)/N) := by
    calc
      _ ≤ (2:ℝ)^(100*q) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = _ := by
        rw [dyadic_rpow_change_base hN]
        have he : (100*(q:ℝ)) = ((100*q:ℕ):ℝ) := by push_cast; ring
        rw [he,Real.rpow_natCast]
  calc
    _ ≤ ((2:ℝ)^N)^(100*(q:ℝ)/N)*((2:ℝ)^N)^(4*((d:ℝ)+1)*lam) :=
      mul_le_mul_of_nonneg_right hwidth (by positivity)
    _ = _ := (Real.rpow_add (by positivity) _ _).symm

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

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileExcess
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual excess profile used by the all-dimensional branch ledger -/

namespace Falconer
open Set
variable {d : ℕ}

theorem profileExcess_lipschitz (Q : DyadicCube d) (ρ : MeasureTheory.Measure (Space d))
    {m : ℝ → ℝ} {N : ℕ} {s lam : ℝ}
    (hreg : Regularization.RegularizedProfileData Q ρ N s lam m) (hN : 0 < N)
    (i j : ℕ) (hi : i ≤ N) (hj : j ≤ N) :
    |profileExcess (d := d) m N i-profileExcess (d := d) m N j| ≤
      (d:ℝ)*|(i:ℝ)-j|/N := by
  have hNR : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  have hunit (k : ℕ) (hk : k ≤ N) : (k:ℝ)/N ∈ Icc (0:ℝ) 1 :=
    ⟨by positivity,(div_le_one hNR).mpr (Nat.cast_le.mpr hk)⟩
  have hsorted (i j : ℕ) (hi : i ≤ N) (hj : j ≤ N) (hij : i ≤ j) :
      |profileExcess (d := d) m N i-profileExcess (d := d) m N j| ≤
        (d:ℝ)*((j:ℝ)-i)/N := by
    have huij : (i:ℝ)/N ≤ (j:ℝ)/N :=
      div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) hNR.le
    have hmij := hreg.monotone (hunit i hi) (hunit j hj) huij
    have hdist := hreg.lipschitz.dist_le_mul ((j:ℝ)/N) (hunit j hj) ((i:ℝ)/N) (hunit i hi)
    simp only [Real.dist_eq,NNReal.coe_natCast,abs_of_nonneg (sub_nonneg.mpr hmij),
      abs_of_nonneg (sub_nonneg.mpr huij)] at hdist
    have hscale : 0 ≤ (d:ℝ)*((j:ℝ)/N-(i:ℝ)/N) := mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr huij)
    have he : (d:ℝ)*((j:ℝ)-i)/N = (d:ℝ)*((j:ℝ)/N-(i:ℝ)/N) := by ring
    rw [he]
    simp only [profileExcess,mul_div_assoc]
    apply abs_le.mpr
    constructor <;> nlinarith
  rcases le_total i j with hij | hji
  · rw [abs_of_nonpos (sub_nonpos.mpr (Nat.cast_le.mpr hij))]
    convert hsorted i j hi hj hij using 1 <;> first | rfl | ring
  · rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hji))]
    exact hsorted j i hj hi hji

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateNear
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Near and terminal bounds for the exact factorized angular states -/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable
open PlanarFalconer (PolicyDescriptor descriptorAnchor)

 theorem profile_jetState_terminal {n K L : ℕ} {D : ℝ} (F : Finset PolicyDescriptor)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2)))
    {m : ℝ → ℝ} {N : ℕ} {s lam : ℝ}
    (hreg : Regularization.RegularizedProfileData Q ρ N s lam m) (hN : 0 < N)
    (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) {a q : ℕ} (ha : a ≤ N)
    (X Y : List (Fin (n+2) → Bool)) (hX : X.length = a) (hY : Y.length = a)
    (v : ℝ) (hv : v ≤ (a:ℝ)+100*q) (Ψ : ℝ → ℝ)
    {W : ℝ} (hW : 0 ≤ W) (hΨ : ∀ t, Ψ t ≤ W) (hsupp : ∀ t, 4 < t → Ψ t = 0) :
    jetStateEnvelope n K L D F F Q ρ (fun t => m (t/N)) N σ J i S A
      (ρ.restrict (Q.descendant X).carrier) (ρ.restrict (Q.descendant Y).carrier)
      (profileModelMass m N a) (profileModelMass m N a) a v Ψ ≤
    (4*W*((descriptorJetBound (n+2) K)^K*A⁻¹)^4*(sphereMeasure (n+2)).real univ^2)*
      ((2:ℝ)^N)^(100*((n+2:ℕ):ℝ)*q/N+4*(((n+2:ℕ):ℝ)+1)*lam) := by
  have hbase : 0 ≤ descriptorJetBound (n+2) K := zero_le_one.trans (descriptorJetBound_one_le _ _)
  have hbound : 0 ≤ (descriptorJetBound (n+2) K)^K*A⁻¹ := by positivity
  apply csSup_le (show (jetStateValues n K L D F F Q ρ (fun t => m (t/N)) N σ J i S A
    (ρ.restrict (Q.descendant X).carrier) (ρ.restrict (Q.descendant Y).carrier)
    (profileModelMass m N a) (profileModelMass m N a) a v Ψ).Nonempty from ⟨0,Or.inl rfl⟩)
  intro h hh
  rcases hh with rfl | ⟨f,g,rfl⟩
  · positivity
  · exact profile_angular_terminal Q ρ hreg hN ha X Y hX hY v hv Ψ hW hΨ hsupp hbound
      (f.value Q ρ (fun t => m (t/N)) N σ J i S A)
      (g.value Q ρ (fun t => m (t/N)) N σ J i S A)
      (f.value_norm_le _ _ _ _ _ _ _ _ hF hA) (g.value_norm_le _ _ _ _ _ _ _ _ hF hA)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateBudgetOrder
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Embedding actual states in the fixed recursive derivative budget -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

theorem jetStateValues_budget_subset {n K K' L L' : ℕ} {D D' : ℝ}
    {F G : Finset PolicyDescriptor} (hK : K ≤ K') (hL : L' ≤ L)
    (hD : 0 ≤ D) (hDD' : D ≤ D')
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (μ ν : Measure (Space (n+2))) (M P a v : ℝ) (Ψ : ℝ → ℝ) :
    jetStateValues n K L D F G Q ρ m N σ J i S A μ ν M P a v Ψ ⊆
      jetStateValues n K' L' D' F G Q ρ m N σ J i S A μ ν M P a v Ψ := by
  intro h hh
  rcases hh with rfl | ⟨f,g,rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨f.relax hK hL hD hDD',g.relax hK hL hD hDD',rfl⟩

theorem jetStateEnvelope_budget_mono {n K K' L L' : ℕ} {D D' : ℝ}
    {F G : Finset PolicyDescriptor} (hK : K ≤ K') (hL : L' ≤ L)
    (hD : 0 ≤ D) (hDD' : D ≤ D')
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (μ ν : Measure (Space (n+2))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)] :
    jetStateEnvelope n K L D F G Q ρ m N σ J i S A μ ν M P a v Ψ ≤
      jetStateEnvelope n K' L' D' F G Q ρ m N σ J i S A μ ν M P a v Ψ := by
  apply csSup_le (show (jetStateValues n K L D F G Q ρ m N σ J i S A μ ν M P a v Ψ).Nonempty
    from ⟨0,Or.inl rfl⟩)
  intro h hh
  exact le_csSup (jetStateValues_bddAbove (K := K') (L := L') (D := D') Q ρ m N σ J i S
    hF hG hA μ ν hM hP a v Ψ)
    (jetStateValues_budget_subset hK hL hD hDD' Q ρ m N σ J i S A μ ν M P a v Ψ hh)

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
-- module Solutions.OAIQ088_FD.Falconer_Recursion_BranchRepresentativeCharges
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem branch_charges_injective {n : ℕ} (start charge : ℕ → ℕ)
    (C : Finset ℕ) (hC : C ⊆ Finset.range n)
    (hstart : MonotoneOn start (Set.Icc 0 n))
    (hcharge : ∀ j ∈ C, start j < charge j ∧ charge j ≤ start (j+1)) :
    Set.InjOn charge C := by
  intro i hi j hj he
  have hiN := Finset.mem_range.mp (hC hi)
  have hjN := Finset.mem_range.mp (hC hj)
  have hci := hcharge i hi
  have hcj := hcharge j hj
  rcases lt_trichotomy i j with hij | hij | hji
  · have hm := hstart (show i+1 ∈ Set.Icc 0 n by constructor <;> omega)
      (show j ∈ Set.Icc 0 n by constructor <;> omega) (by omega : i+1 ≤ j)
    omega
  · exact hij
  · have hm := hstart (show j+1 ∈ Set.Icc 0 n by constructor <;> omega)
      (show i ∈ Set.Icc 0 n by constructor <;> omega) (by omega : j+1 ≤ i)
    omega

theorem branch_representative_charges_bound (A : ℕ → ℝ) (N q n : ℕ)
    (start charge : ℕ → ℕ) (C : Finset ℕ) (hC : C ⊆ Finset.range n)
    (hstart : MonotoneOn start (Set.Icc 0 n))
    (hcharge : ∀ j ∈ C, start j < charge j ∧ charge j ≤ start (j+1))
    (hrep : ∀ j ∈ C, charge j ∈ policyRepresentatives A N q) :
    C.card ≤ (policyRepresentatives A N q).card ∧ C.card ≤ N/q+1 := by
  have hi := branch_charges_injective start charge C hC hstart hcharge
  have hc : C.card ≤ (policyRepresentatives A N q).card := by
    calc
      _ = (C.image charge).card := (Finset.card_image_of_injOn hi).symm
      _ ≤ _ := Finset.card_le_card (by
        intro p hp
        obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hp
        exact hrep j hj)
  exact ⟨hc,hc.trans (policy_representatives_card A N q)⟩

theorem source_representatives_real_bound (A : ℕ → ℝ) {N : ℕ}
    (hN : 0 < N) {kap : ℝ} (hkap : 0 < kap) (hkap1 : kap ≤ 1) :
    ((policyRepresentatives A N (sourcePolicyBlock N kap)).card:ℝ) ≤ 2/kap := by
  let q := sourcePolicyBlock N kap
  have hq : 0 < q := sourcePolicyBlock_pos hN hkap
  have hqR : (0:ℝ) < q := Nat.cast_pos.mpr hq
  have hc : ((policyRepresentatives A N q).card:ℝ) ≤ ((N/q:ℕ):ℝ)+1 := by
    exact_mod_cast policy_representatives_card A N q
  have hmul : ((N/q:ℕ):ℝ)*(q:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.div_mul_le_self N q
  have hdiv : ((N/q:ℕ):ℝ) ≤ (N:ℝ)/(q:ℝ) := (le_div_iff₀ hqR).mpr hmul
  have hblock := source_policy_block_lower N kap
  have hrat : (N:ℝ)/(q:ℝ) ≤ 1/kap := (div_le_div_iff₀ hqR hkap).mpr (by
    change (N:ℝ)*kap ≤ 1*(sourcePolicyBlock N kap:ℝ)
    nlinarith)
  have hone : 1 ≤ 1/kap := (le_div_iff₀ hkap).mpr (by simpa using hkap1)
  change ((policyRepresentatives A N q).card:ℝ) ≤ 2/kap
  have he : 2/kap = 1/kap+1/kap := by ring
  rw [he]
  linarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_BranchTransitions
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

namespace BranchState

theorem valid_depths {N : ℕ} {sig : ℝ} {s : BranchState} (h : s.Valid N sig) :
    s.start ≤ s.finish ∧ s.finish ≤ N := by
  cases s <;> simp only [Valid,start,finish] at *
  · exact h
  · omega

end BranchState

namespace BranchStep
variable {A : ℕ → ℝ} {N q : ℕ} {sig : ℝ}
variable {s u : BranchState} {label : BranchLabel}

theorem nonterminal (h : BranchStep A N q sig s label u) : s.start+100*q < s.finish := by
  cases h <;> assumption

theorem nested (h : BranchStep A N q sig s label u) (hq : 0 < q)
    (hv : s.Valid N sig) : s.start ≤ u.start ∧ u.finish ≤ s.finish := by
  cases h with
  | suffix hw _ =>
    have hp := policyDepth_interior A hq (policyBlocks_nonempty hq hv.2 hw)
    simp only [BranchState.start,BranchState.finish]
    omega
  | low _ hm _ =>
    have hm := Finset.mem_Ioc.mp hm
    exact ⟨le_rfl,hm.2⟩
  | high hw _ hm _ =>
    have hp := policyDepth_interior A hq (policyBlocks_nonempty hq hv.2 hw)
    have hm := Finset.mem_Ioc.mp hm
    exact ⟨by dsimp [BranchState.start]; omega,hm.2⟩
  | near _ hs => exact ⟨hs.le,le_rfl⟩
  | far _ _ hm =>
    have hm := Finset.mem_Icc.mp hm
    exact ⟨by dsimp [BranchState.start]; omega,le_rfl⟩
  | direct _ hw => exact ⟨hw.anchor_gt.le,le_rfl⟩

theorem index_change (h : BranchStep A N q sig s label u) :
    u.index = s.index + (if label = .suffix ∨ label = .low ∨ label = .far then 1 else 0) := by
  cases h <;> simp [BranchState.index]

theorem episode_balance (h : BranchStep A N q sig s label u) :
    u.angular + (if label = .far then 1 else 0) =
      s.angular + (if label = .high then 1 else 0) := by
  cases h <;> simp [BranchState.angular]

theorem suffix_decrease (h : BranchStep A N q sig s .suffix u) (hq : 0 < q)
    (hv : s.Valid N sig) : u.finish+q ≤ s.finish := by
  cases h with
  | suffix hw _ =>
    have hp := policyDepth_interior A hq (policyBlocks_nonempty hq hv.2 hw)
    dsimp only [BranchState.finish]
    omega

theorem low_decrease (h : BranchStep A N q sig s .low u) :
    (u.finish:ℝ)+sig*N ≤ s.finish := by
  cases h with
  | low _ _ hg => dsimp only [BranchState.finish]; linarith

theorem graph_charge (h : BranchStep A N q sig s label u) (hq : 0 < q)
    (hv : s.Valid N sig) (hg : label = .high ∨ label = .direct) :
    s.start < u.start ∧ u.start ∈ policyRepresentatives A N q := by
  cases h with
  | high hw _ _ _ =>
    have hn := policyBlocks_nonempty hq hv.2 hw
    have hp := policyDepth_interior A hq hn
    exact ⟨by dsimp [BranchState.start]; omega,policyDepth_mem_representatives A hn⟩
  | direct _ hw =>
    exact ⟨hw.anchor_gt,policyDescriptor_anchor_mem A hq (Finset.mem_filter.mp hw.mem).1⟩
  | _ => simp at hg

end BranchStep

theorem near_uncharged_next_direct {A : ℕ → ℝ} {N q : ℕ} {sig : ℝ}
    (hq : 0 < q) (hceil : ⌈10*sig*(N:ℝ)⌉₊ < q)
    {s u w : BranchState} {label : BranchLabel}
    (h : BranchStep A N q sig s .near u) (hn : ¬ ChargedNear A N q s u)
    (hnext : BranchStep A N q sig u label w) : label = .direct := by
  have hw := hnext.nonterminal
  cases h with
  | near hwide hnear =>
    obtain ht | hp | he := actual_near_progress A hq hceil hnear
    · exact (not_lt_of_ge ht hw).elim
    · obtain ⟨e,hm,hL,ha,hb,_⟩ := hp
      exact (hn ⟨hw,e,hm,hL,ha,hb⟩).elim
    · simp only [BranchState.finish] at he
      cases hnext with
      | near _ hs =>
        simp only [BranchState.nearDepth,BranchState.finish,BranchState.descriptors] at hs
        rw [he.2] at hs
        exact (Nat.lt_irrefl _ hs).elim
      | far _ hs _ =>
        simp only [BranchState.nearDepth,BranchState.finish,BranchState.descriptors] at hs
        rw [he.2] at hs
        exact (Nat.lt_irrefl _ hs).elim
      | direct _ _ => rfl

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_BranchCounts
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem branchCount_card (label : ℕ → BranchLabel) (n : ℕ) (kind : BranchLabel) :
    branchCount label n kind = ((Finset.range n).filter fun j => label j = kind).card := by
  simp [branchCount]

theorem branchCount_succ (label : ℕ → BranchLabel) (n : ℕ) (kind : BranchLabel) :
    branchCount label (n+1) kind = branchCount label n kind + if label n = kind then 1 else 0 := by
  simp only [branchCount,Finset.sum_range_succ]

namespace PolicyBranch
variable {A : ℕ → ℝ} {N q n : ℕ} {sig : ℝ}

theorem nested (b : PolicyBranch A N q sig n) (hq : 0 < q) :
    MonotoneOn (fun j => (b.state j).start) (Set.Icc 0 n) ∧
    AntitoneOn (fun j => (b.state j).finish) (Set.Icc 0 n) := by
  have hpair : ∀ j k, j ≤ k → k ≤ n →
      (b.state j).start ≤ (b.state k).start ∧ (b.state k).finish ≤ (b.state j).finish := by
    intro j k hjk hkn
    induction k, hjk using Nat.le_induction with
    | base => exact ⟨le_rfl,le_rfl⟩
    | succ k hjk ih =>
      have hp := ih (by omega)
      have hs := (b.step k (by omega)).nested hq (b.valid k (by omega))
      exact ⟨hp.1.trans hs.1,hs.2.trans hp.2⟩
  exact ⟨fun _ _ _ hk hjk => (hpair _ _ hjk hk.2).1,
    fun _ _ _ hk hjk => (hpair _ _ hjk hk.2).2⟩

theorem charges_card (b : PolicyBranch A N q sig n) :
    b.charges.card = branchCount b.label n .high + branchCount b.label n .direct + b.chargedNear.card := by
  classical
  simp only [charges,chargedNear,Finset.card_filter,branchCount,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  cases b.label j <;> simp

theorem charges_have_representatives (b : PolicyBranch A N q sig n) (hq : 0 < q)
    {j : ℕ} (hj : j ∈ b.charges) :
    ∃ p ∈ policyRepresentatives A N q, (b.state j).start < p ∧ p ≤ (b.state (j+1)).start := by
  classical
  obtain ⟨hj,hlabel⟩ := Finset.mem_filter.mp hj
  have hjn := Finset.mem_range.mp hj
  rcases hlabel with hh | hd | ⟨hn,he⟩
  · have hg := (b.step j hjn).graph_charge hq (b.valid j hjn.le) (Or.inl hh)
    exact ⟨_,hg.2,hg.1,le_rfl⟩
  · have hg := (b.step j hjn).graph_charge hq (b.valid j hjn.le) (Or.inr hd)
    exact ⟨_,hg.2,hg.1,le_rfl⟩
  · obtain ⟨_,e,he,_,ha,hp⟩ := he
    have hr : descriptorAnchor e ∈ policyRepresentatives A N q := by
      cases hs : b.state j <;> rw [hs] at he
      · exact policyDescriptor_anchor_mem A hq he
      · exact policyDescriptor_anchor_mem A hq (Finset.mem_filter.mp he).1
    exact ⟨descriptorAnchor e,hr,ha,hp⟩

theorem representative_counts (b : PolicyBranch A N q sig n) (hq : 0 < q) :
    branchCount b.label n .high + branchCount b.label n .direct + b.chargedNear.card ≤
        (policyRepresentatives A N q).card ∧
      (policyRepresentatives A N q).card ≤ N/q+1 := by
  classical
  let charge := fun j => if hj : j ∈ b.charges then
    Classical.choose (b.charges_have_representatives hq hj) else 0
  have hspec (j : ℕ) (hj : j ∈ b.charges) :
      charge j ∈ policyRepresentatives A N q ∧
      (b.state j).start < charge j ∧ charge j ≤ (b.state (j+1)).start := by
    simpa only [charge,dite_eq_left hj] using Classical.choose_spec (b.charges_have_representatives hq hj)
  have hb := branch_representative_charges_bound A N q n (fun j => (b.state j).start)
    charge b.charges (Finset.filter_subset _ _) (b.nested hq).1
    (fun j hj => (hspec j hj).2) (fun j hj => (hspec j hj).1)
  exact ⟨by rw [← b.charges_card]; exact hb.1,policy_representatives_card A N q⟩

theorem near_count (b : PolicyBranch A N q sig n) (hq : 0 < q)
    (hceil : ⌈10*sig*(N:ℝ)⌉₊ < q) :
    branchCount b.label n .near ≤ b.chargedNear.card + branchCount b.label n .direct + 1 := by
  classical
  let U := (Finset.range n).filter fun j => b.label j = .near ∧
    ¬ ChargedNear A N q (b.state j) (b.state (j+1))
  have hpartition : branchCount b.label n .near = b.chargedNear.card+U.card := by
    simp only [chargedNear,U,Finset.card_filter,branchCount,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hl : b.label j = .near <;>
      by_cases hc : ChargedNear A N q (b.state j) (b.state (j+1)) <;> simp [hl,hc]
  have hu : U.card ≤ branchCount b.label n .direct+1 := by
    rw [branchCount_card]
    let D := ((Finset.range n).filter fun j => b.label j = .direct)
    have hmap : U.image Nat.succ ⊆ insert n D := by
      intro k hk
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hjn,hn,hc⟩ := Finset.mem_filter.mp hj
      have hjn := Finset.mem_range.mp hjn
      by_cases he : j+1 = n
      · exact Finset.mem_insert.mpr (Or.inl he)
      · apply Finset.mem_insert.mpr
        apply Or.inr
        have hnext := near_uncharged_next_direct hq hceil
          (by simpa only [hn] using b.step j hjn) hc (b.step (j+1) (by omega))
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hnext⟩
    calc
      U.card = (U.image Nat.succ).card := (Finset.card_image_of_injective _ Nat.succ_injective).symm
      _ ≤ (insert n D).card := Finset.card_le_card hmap
      _ ≤ D.card+1 := Finset.card_insert_le _ _
  omega

theorem episode_identity (b : PolicyBranch A N q sig n) :
    (b.state n).angular + branchCount b.label n .far =
      (b.state 0).angular + branchCount b.label n .high := by
  induction n with
  | zero => simp [branchCount]
  | succ n ih =>
    have hp := ih (b.initialSegment n (by omega))
    have hs := (b.step n (by omega)).episode_balance
    dsimp only [initialSegment] at hp
    rw [branchCount_succ,branchCount_succ]
    omega

theorem far_count (b : PolicyBranch A N q sig n) :
    branchCount b.label n .far ≤ branchCount b.label n .high+1 := by
  have hi := b.episode_identity
  have hzero : (b.state 0).angular ≤ 1 := by cases b.state 0 <;> simp [BranchState.angular]
  omega

theorem suffix_total_decrease (b : PolicyBranch A N q sig n) (hq : 0 < q) :
    (b.state n).finish + branchCount b.label n .suffix*q ≤ (b.state 0).finish := by
  induction n with
  | zero => simp [branchCount]
  | succ n ih =>
    have hp := ih (b.initialSegment n (by omega))
    dsimp only [initialSegment] at hp
    have hs := (b.step n (by omega)).nested hq (b.valid n (by omega))
    rw [branchCount_succ,Nat.add_mul]
    by_cases hl : b.label n = .suffix
    · have hd := BranchStep.suffix_decrease (by simpa only [hl] using b.step n (by omega)) hq
        (b.valid n (by omega))
      simp only [hl,ite_true, if_true,one_mul]
      omega
    · simp only [hl,ite_false, if_false,zero_mul]
      omega

theorem low_total_decrease (b : PolicyBranch A N q sig n) (hq : 0 < q) :
    ((b.state n).finish:ℝ) + (branchCount b.label n .low:ℝ)*(sig*N) ≤ (b.state 0).finish := by
  induction n with
  | zero => simp [branchCount]
  | succ n ih =>
    have hp := ih (b.initialSegment n (by omega))
    dsimp only [initialSegment] at hp
    have hs := (b.step n (by omega)).nested hq (b.valid n (by omega))
    have hsR : ((b.state (n+1)).finish:ℝ) ≤ (b.state n).finish := Nat.cast_le.mpr hs.2
    rw [branchCount_succ]
    by_cases hl : b.label n = .low
    · have hd := BranchStep.low_decrease (by simpa only [hl] using b.step n (by omega))
      simp only [hl,ite_true, if_true,Nat.cast_add,Nat.cast_one]
      nlinarith
    · simp only [hl,ite_false, if_false,add_zero]
      linarith

theorem index_identity (b : PolicyBranch A N q sig n) :
    (b.state n).index = (b.state 0).index + branchCount b.label n .suffix +
      branchCount b.label n .low + branchCount b.label n .far := by
  induction n with
  | zero => simp [branchCount]
  | succ n ih =>
    have hp := ih (b.initialSegment n (by omega))
    dsimp only [initialSegment] at hp
    have hs := (b.step n (by omega)).index_change
    rw [branchCount_succ,branchCount_succ,branchCount_succ,hs,hp]
    cases b.label n <;> simp <;> omega

end PolicyBranch

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_BranchValidity
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem high_depth_gap {N q t v : ℕ} {sig : ℝ} (hv : v ≤ t)
    (hgap : (t:ℝ)-v < sig*N) (hslack : sig*(N:ℝ) ≤ q) : t-v ≤ q := by
  have hcast : ((t-v:ℕ):ℝ) = (t:ℝ)-v := Nat.cast_sub hv
  exact Nat.cast_le.mp (by rw [hcast]; exact hgap.le.trans hslack)

theorem BranchStep.valid_successor {A : ℕ → ℝ} {N q : ℕ} {sig : ℝ}
    (hq : 0 < q) (hslack : sig*(N:ℝ) ≤ q)
    (hbuffer : ∀ L t a : ℕ, a < t-2*sourceFarBuffer N L sig →
      t-2*sourceFarBuffer N L sig+5 < t)
    {s u : BranchState} {label : BranchLabel}
    (h : BranchStep A N q sig s label u) (hv : s.Valid N sig) : u.Valid N sig := by
  cases h with
  | suffix hw _ =>
    have hp := policyDepth_interior A hq (policyBlocks_nonempty hq hv.2 hw)
    dsimp only [BranchState.Valid] at *
    omega
  | low _ hm _ =>
    have hm := Finset.mem_Ioc.mp hm
    dsimp only [BranchState.Valid] at *
    omega
  | high hw hs hm hg =>
    have hm := Finset.mem_Ioc.mp hm
    have hgap := high_depth_gap hm.2 hg hslack
    have hp := actual_prefix_policy_payment A hq hv.2 hw hs hm.2 hgap
    have hi := policyDepth_interior A hq (policyBlocks_nonempty hq hv.2 hw)
    exact ⟨by omega,by omega,hm.2,hv.2,by linarith⟩
  | near _ hs =>
    dsimp only [BranchState.Valid,BranchState.nearDepth,BranchState.finish,BranchState.descriptors] at *
    exact ⟨by omega,Nat.sub_le _ _,hv.2.2⟩
  | far _ hs hm =>
    have hb := hbuffer _ _ _ hs
    have hm := Finset.mem_Icc.mp hm
    dsimp only [BranchState.Valid,BranchState.nearDepth,BranchState.finish,BranchState.descriptors] at *
    exact ⟨by omega,by omega⟩
  | direct _ hw =>
    exact ⟨hv.1.trans hw.anchor_gt.le,hw.anchor_lt.le,hv.2.2⟩

theorem uniform_branch_successor_validity {sig kap : ℝ}
    (hsig : 0 < sig) (hkap : 0 < kap) (hgap : sig < kap/1000) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ A : ℕ → ℝ,
      ∀ s u : BranchState, ∀ label : BranchLabel,
      s.Valid N sig → BranchStep A N (sourcePolicyBlock N kap) sig s label u →
      u.Valid N sig ∧ s.start ≤ u.start ∧ u.finish ≤ s.finish := by
  obtain ⟨N₁,hN₁,h₁⟩ := uniform_source_ceiling_slack hsig hgap
  obtain ⟨N₂,h₂⟩ := uniform_source_far_buffer hsig
  refine ⟨max N₁ N₂,by omega,?_⟩
  intro N hN A s u label hv h
  have hq := sourcePolicyBlock_pos (by omega : 0 < N) hkap
  have hb : ∀ L t a : ℕ, a < t-2*sourceFarBuffer N L sig →
      t-2*sourceFarBuffer N L sig+5 < t := by
    intro L t a ha
    have hh := h₂ N (by omega) L t a ha
    omega
  exact ⟨h.valid_successor hq (h₁ N (by omega)).2.2 hb hv,h.nested hq hv⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_BranchPotential
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem BranchStep.paid_width {A : ℕ → ℝ} {N q : ℕ} {sig : ℝ}
    {s u : BranchState} {label : BranchLabel} (h : BranchStep A N q sig s label u)
    (hq : 0 < q) (hv : s.Valid N sig) (hslack : sig*(N:ℝ) ≤ q)
    (hc : label = .suffix ∨ label = .high ∨ label = .direct) : u.start+10*q ≤ u.finish := by
  cases h with
  | suffix hw hs => exact (actual_suffix_policy_payment A hq hv.2 hw hs).1
  | high hw hs hm hg =>
    have hm := Finset.mem_Ioc.mp hm
    exact (actual_prefix_policy_payment A hq hv.2 hw hs hm.2 (high_depth_gap hm.2 hg hslack)).1
  | direct _ he => exact he.width
  | _ => simp at hc

theorem BranchStep.potential_payment {A : ℕ → ℝ} {N q : ℕ} {sig : ℝ}
    {s u : BranchState} {label : BranchLabel} (h : BranchStep A N q sig s label u)
    (hq : 0 < q) (hv : s.Valid N sig) (hslack : sig*(N:ℝ) ≤ q)
    (hu : u.start+10*q ≤ u.finish) :
    potential A s.start s.finish (10*q)+branchCost A s label u ≤
      potential A u.start u.finish (10*q) := by
  have hn := h.nested hq hv
  have hm := potential_mono A (by omega : 0 < 10*q) hu hn.1 hn.2
  cases h with
  | suffix hw hs => exact (actual_suffix_policy_payment A hq hv.2 hw hs).2
  | high hw hs hmem hg =>
    have hmem := Finset.mem_Ioc.mp hmem
    exact (actual_prefix_policy_payment A hq hv.2 hw hs hmem.2 (high_depth_gap hmem.2 hg hslack)).2
  | direct _ he => exact he.payment
  | _ => simpa only [branchCost,add_zero] using hm

theorem BranchStep.short_cost_zero {A : ℕ → ℝ} {N q : ℕ} {sig : ℝ}
    {s u : BranchState} {label : BranchLabel} (h : BranchStep A N q sig s label u)
    (hq : 0 < q) (hv : s.Valid N sig) (hslack : sig*(N:ℝ) ≤ q)
    (hu : u.finish < u.start+10*q) : branchCost A s label u = 0 := by
  have hc : ¬ (label = .suffix ∨ label = .high ∨ label = .direct) := by
    intro hl
    exact (not_le_of_gt hu) (h.paid_width hq hv hslack hl)
  cases label <;> simp_all [branchCost]

namespace PolicyBranch
variable {A : ℕ → ℝ} {N q n : ℕ} {sig : ℝ}

theorem costs_le_potential (b : PolicyBranch A N q sig n) (hq : 0 < q)
    (hslack : sig*(N:ℝ) ≤ q) (hfinal : (b.state n).start+10*q ≤ (b.state n).finish) :
    ∑ j ∈ Finset.range n, branchCost A (b.state j) (b.label j) (b.state (j+1)) ≤
      potential A (b.state n).start (b.state n).finish (10*q)-
        potential A (b.state 0).start (b.state 0).finish (10*q) := by
  apply branch_cost_bound (fun j => potential A (b.state j).start (b.state j).finish (10*q))
    (fun j => branchCost A (b.state j) (b.label j) (b.state (j+1))) n
  intro j hj
  apply (b.step j hj).potential_payment hq (b.valid j hj.le) hslack
  by_cases he : j+1 = n
  · simpa only [he] using hfinal
  · have hw := (b.step (j+1) (by omega)).nonterminal
    omega

end PolicyBranch

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_SourceBranchDepth
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem branch_count_total (label : ℕ → BranchLabel) (n : ℕ) :
    branchNonlowCount label n + branchCount label n .low = n := by
  induction n with
  | zero => simp [branchNonlowCount,branchCount]
  | succ n ih =>
    simp only [branchNonlowCount] at *
    simp only [branchCount_succ]
    cases h : label n <;> simp <;> omega

theorem source_branch_count_bounds {A : ℕ → ℝ} {N n : ℕ} {sig kap : ℝ}
    (hN : 0 < N) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (hceil : ⌈10*sig*(N:ℝ)⌉₊ < sourcePolicyBlock N kap)
    (b : PolicyBranch A N (sourcePolicyBlock N kap) sig n) :
    (branchNonlowCount b.label n:ℝ) ≤ 20/kap ∧
      (branchCount b.label n .low:ℝ) ≤ 1/sig ∧ (n:ℝ) ≤ 20/kap+1/sig := by
  have hq := sourcePolicyBlock_pos hN hkap
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hstart := BranchState.valid_depths (b.valid 0 (Nat.zero_le _))
  have hS := b.suffix_total_decrease hq
  have hSR : (branchCount b.label n .suffix:ℝ)*(sourcePolicyBlock N kap:ℝ) ≤ N := by
    exact_mod_cast (show branchCount b.label n .suffix*sourcePolicyBlock N kap ≤ N by omega)
  have hblock := source_policy_block_lower N kap
  have hSb := mul_le_mul_of_nonneg_left hblock (Nat.cast_nonneg (branchCount b.label n .suffix))
  have hSbound : (branchCount b.label n .suffix:ℝ) ≤ 1/kap := by
    apply (le_div_iff₀ hkap).mpr
    apply (mul_le_mul_iff_left₀ hNR).mp
    nlinarith [hSb.trans hSR]
  have hL := b.low_total_decrease hq
  have hLR : ((b.state 0).finish:ℝ) ≤ N := Nat.cast_le.mpr hstart.2
  have hLbound : (branchCount b.label n .low:ℝ) ≤ 1/sig := by
    apply (le_div_iff₀ hsig).mpr
    apply (mul_le_mul_iff_left₀ hNR).mp
    nlinarith [show (0:ℝ) ≤ (b.state n).finish from Nat.cast_nonneg _]
  have hG := (b.representative_counts hq).1
  have hK := b.near_count hq hceil
  have hF := b.far_count
  have hB := source_representatives_real_bound A hN hkap hkap1
  have hnonlow : branchNonlowCount b.label n ≤
      2*(policyRepresentatives A N (sourcePolicyBlock N kap)).card + branchCount b.label n .suffix+2 := by
    dsimp only [branchNonlowCount]
    omega
  have hnonlowR : (branchNonlowCount b.label n:ℝ) ≤
      2*((policyRepresentatives A N (sourcePolicyBlock N kap)).card:ℝ) +
        (branchCount b.label n .suffix:ℝ)+2 := by exact_mod_cast hnonlow
  have hone : 1 ≤ 1/kap := (le_div_iff₀ hkap).mpr (by simpa using hkap1)
  have hbound : (branchNonlowCount b.label n:ℝ) ≤ 20/kap := by
    have he : 20/kap = 20*(1/kap) := by ring
    have he2 : 2/kap = 2*(1/kap) := by ring
    rw [he2] at hB
    rw [he]
    linarith
  refine ⟨hbound,hLbound,?_⟩
  have ht : (branchNonlowCount b.label n:ℝ)+(branchCount b.label n .low:ℝ) = n := by
    exact_mod_cast branch_count_total b.label n
  linarith

theorem source_smoothing_reserve {sig kap : ℝ} (hsig : 0 < sig) (hkap : 0 < kap) :
    1+20/kap+1/sig < (sourceSmoothingLevels sig kap:ℝ) := by
  have hceil : 100*(1/sig+1/kap)+100 ≤ (sourceSmoothingLevels sig kap:ℝ) := Nat.le_ceil _
  have he : 20/kap = 20*(1/kap) := by ring
  rw [he]
  have hk : 0 < 1/kap := by positivity
  have hs : 0 < 1/sig := by positivity
  linarith

theorem source_branch_index_bound {A : ℕ → ℝ} {N n : ℕ} {sig kap : ℝ}
    (hN : 0 < N) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (hceil : ⌈10*sig*(N:ℝ)⌉₊ < sourcePolicyBlock N kap)
    (b : PolicyBranch A N (sourcePolicyBlock N kap) sig n) (hi : (b.state 0).index = 0)
    {j : ℕ} (hj : j ≤ n) :
    ((b.state j).index:ℝ)+1 ≤ 1+20/kap+1/sig ∧ (b.state j).index+1 < sourceSmoothingLevels sig kap := by
  let c := b.initialSegment j hj
  have hc := source_branch_count_bounds hN hsig hkap hkap1 hceil c
  have hind := c.index_identity
  change (b.state j).index = (b.state 0).index + branchCount b.label j .suffix +
    branchCount b.label j .low + branchCount b.label j .far at hind
  rw [hi] at hind
  have hn : (b.state j).index ≤ branchNonlowCount b.label j + branchCount b.label j .low := by
    dsimp only [branchNonlowCount]
    omega
  have hnR : ((b.state j).index:ℝ) ≤ (branchNonlowCount b.label j:ℝ)+(branchCount b.label j .low:ℝ) := by
    exact_mod_cast hn
  change (branchNonlowCount b.label j:ℝ) ≤ _ ∧ (branchCount b.label j .low:ℝ) ≤ _ ∧ _ at hc
  have hb : ((b.state j).index:ℝ)+1 ≤ 1+20/kap+1/sig := by linarith [hc.1,hc.2.1]
  refine ⟨hb,?_⟩
  have hh := hb.trans_lt (source_smoothing_reserve hsig hkap)
  exact_mod_cast hh

theorem uniform_source_branch_depth {sig kap : ℝ}
    (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1) (hgap : sig < kap/1000) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ A : ℕ → ℝ, ∀ n : ℕ,
      ∀ b : PolicyBranch A N (sourcePolicyBlock N kap) sig n,
      (b.state 0).index = 0 →
      (branchNonlowCount b.label n:ℝ) ≤ 20/kap ∧
      (branchCount b.label n .low:ℝ) ≤ 1/sig ∧ (n:ℝ) ≤ 20/kap+1/sig ∧
      ∀ j ≤ n, ((b.state j).index:ℝ)+1 ≤ 1+20/kap+1/sig ∧
        (b.state j).index+1 < sourceSmoothingLevels sig kap := by
  obtain ⟨N₀,hN₀,h₀⟩ := uniform_source_ceiling_slack hsig hgap
  refine ⟨N₀,hN₀,?_⟩
  intro N hN A n b hi
  have hNp : 0 < N := hN₀.trans_le hN
  have hc := source_branch_count_bounds hNp hsig hkap hkap1 (h₀ N hN).1 b
  exact ⟨hc.1,hc.2.1,hc.2.2,fun j hj => source_branch_index_bound
    hNp hsig hkap hkap1 (h₀ N hN).1 b hi hj⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_BranchExponentAlgebra
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem branch_nonlow_indicator_sum (label : ℕ → BranchLabel) (n : ℕ) :
    (∑ j ∈ Finset.range n, if label j = .low then 0 else 1) = branchNonlowCount label n := by
  have htot := branch_count_total label n
  have hsum : branchCount label n .low +
      (∑ j ∈ Finset.range n, if label j = .low then 0 else 1) = n := by
    simp only [branchCount,← Finset.sum_add_distrib]
    calc
      _ = ∑ _j ∈ Finset.range n, (1:ℕ) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : label j = .low <;> simp [hj]
      _ = n := by simp
  omega

theorem branch_nonlow_loss_sum (label : ℕ → BranchLabel) (n : ℕ) (loss : ℝ) :
    (∑ j ∈ Finset.range n, if label j = .low then 0 else loss) =
      (branchNonlowCount label n:ℝ)*loss := by
  have hcast := congrArg (fun k : ℕ => (k:ℝ)) (branch_nonlow_indicator_sum label n)
  simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,Nat.cast_one] at hcast
  calc
    _ = ∑ j ∈ Finset.range n, (if label j = .low then (0:ℝ) else 1)*loss := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : label j = .low <;> simp [hj]
    _ = _ := by rw [← Finset.sum_mul,hcast]

theorem branch_exponent_sum (A : ℕ → ℝ) (lam sig eps : ℝ)
    (state : ℕ → BranchState) (label : ℕ → BranchLabel) (n : ℕ) :
    (∑ j ∈ Finset.range n, branchExponent A lam sig eps (state j) (label j) (state (j+1))) =
      2*A (state 0).start-2*A (state n).start+
      (∑ j ∈ Finset.range n, branchCost A (state j) (label j) (state (j+1)))+
      (branchNonlowCount label n:ℝ)*(4000*(lam+sig))+(n:ℝ)*eps := by
  simp only [branchExponent,Finset.sum_add_distrib]
  rw [profile_increments_telescope A (fun j => (state j).start) n,branch_nonlow_loss_sum]
  simp

end PlanarFalconer

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

theorem dimensionalBranchReserve_nonneg (d : ℕ) {lam σ : ℝ}
    (hlam : 0 ≤ lam) (hσ : 0 ≤ σ) : 0 ≤ dimensionalBranchReserve d lam σ := by
  unfold dimensionalBranchReserve
  positivity

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_PolicyAngularBranches
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The proved angular steps use the scheduled scalar branches -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (BranchState BranchStep BranchLabel branchExponent branchCost descriptorAnchor)

namespace PolicyJetData
variable {m : ℕ}

theorem branchState_valid (P : PolicyJetData m) (hat : P.a ≤ P.t)
    (hbase : (P.t₀:ℝ) ≤ P.t+P.σ*P.N) : P.branchState.Valid P.N P.σ :=
  ⟨P.base_left,hat,P.base_right,P.base_N,hbase⟩

theorem direct_branch (P : PolicyJetData m) (hwide : P.a+100*P.q < P.t)
    {d : PlanarFalconer.PolicyDescriptor}
    (hd : PlanarFalconer.DirectPolicyWitness P.policy P.N P.q P.a₀ P.t₀ P.a P.t P.σ d) :
    BranchStep P.policy P.N P.q P.σ P.branchState .direct
      (.H P.a₀ P.t₀ (descriptorAnchor d) P.t P.i) := BranchStep.direct hwide hd

theorem near_branch (P : PolicyJetData m) (hwide : P.a+100*P.q < P.t)
    (hnear : P.a < P.splitDepth) :
    BranchStep P.policy P.N P.q P.σ P.branchState .near
      (.H P.a₀ P.t₀ P.splitDepth P.t P.i) := BranchStep.near hwide hnear

theorem far_branch (P : PolicyJetData m) (hwide : P.a+100*P.q < P.t)
    (hnear : P.a < P.splitDepth) {b : ℕ}
    (hb : b ∈ Finset.Icc (P.a+9) (P.splitDepth+6)) :
    BranchStep P.policy P.N P.q P.σ P.branchState .far (.D b P.t (P.i+1)) :=
  BranchStep.far hwide hnear hb

theorem directWeight_eq_branchExponent (P : PolicyJetData m) (p : ℕ) (lam σ ε : ℝ)
    (hprofile : P.policy = profileExcess (d := m+3) P.profile P.N) :
    P.directWeight p lam σ ε = ((2:ℝ)^P.N)^(branchExponent P.policy
      (dimensionalBranchReserve (m+3) lam σ) σ ε P.branchState .direct
        (.H P.a₀ P.t₀ p P.t P.i)) := by
  simp only [directWeight,branchExponent,branchCost,branchState,BranchState.start,
    reduceCtorEq,ite_false, if_false,hprofile]

theorem nearWeight_eq_branchExponent (P : PolicyJetData m) (lam σ ε : ℝ)
    (hprofile : P.policy = profileExcess (d := m+3) P.profile P.N) :
    P.farWeight P.splitDepth lam σ ε = ((2:ℝ)^P.N)^(branchExponent P.policy
      (dimensionalBranchReserve (m+3) lam σ) σ ε P.branchState .near
        (.H P.a₀ P.t₀ P.splitDepth P.t P.i)) := by
  simp only [farWeight,branchExponent,branchCost,branchState,BranchState.start,
    reduceCtorEq,ite_false, if_false,hprofile,add_zero]

theorem farWeight_eq_branchExponent (P : PolicyJetData m) (b : ℕ) (lam σ ε : ℝ)
    (hprofile : P.policy = profileExcess (d := m+3) P.profile P.N) :
    P.farWeight b lam σ ε = ((2:ℝ)^P.N)^(branchExponent P.policy
      (dimensionalBranchReserve (m+3) lam σ) σ ε P.branchState .far (.D b P.t (P.i+1))) := by
  simp only [farWeight,branchExponent,branchCost,branchState,BranchState.start,
    reduceCtorEq,ite_false, if_false,hprofile,add_zero]

end PolicyJetData
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PolicySuffixRecurrence
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual positive suffix reduction with the scalar branch weight -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (policyDepth)

namespace PolicyJetData
variable {m : ℕ}

theorem suffixWeight_eq_branchExponent (P : PolicyJetData m) (p : ℕ) (lam σ ε : ℝ)
    (hprofile : P.policy = profileExcess (d := m+3) P.profile P.N) :
    P.suffixWeight p lam σ ε = ((2:ℝ)^P.N)^(PlanarFalconer.branchExponent P.policy
      (dimensionalBranchReserve (m+3) lam σ) σ ε (.D P.a P.t P.i) (.suffix) (.D P.a p (P.i+1))) := by
  unfold suffixWeight PlanarFalconer.branchExponent PlanarFalconer.branchCost
  simp only [PlanarFalconer.BranchState.start,PlanarFalconer.BranchState.finish,
    sub_self,mul_zero,zero_add,reduceCtorEq,ite_false, if_false,hprofile]
  rfl

end PolicyJetData

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_PolicyPositiveBranches
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete positive successors in the weighted branch tree -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (BranchState BranchStep BranchLabel branchExponent branchCost policyDepth)

namespace PolicyJetData
variable {m : ℕ}

theorem positiveBranchState_valid (P : PolicyJetData m) (hat : P.a ≤ P.t) :
    P.positiveBranchState.Valid P.N P.σ := ⟨hat,P.base_right.trans P.base_N⟩

theorem positive_low_branch (P : PolicyJetData m) (hwide : P.a+100*P.q < P.t)
    {v : ℕ} (hv : v ∈ Finset.Ioc P.a P.t) (hgap : P.σ*P.N ≤ (P.t:ℝ)-v) :
    BranchStep P.policy P.N P.q P.σ P.positiveBranchState .low
      (P.positiveSuccessor v ((Finset.mem_Ioc.mp hv).2.trans P.base_right) (P.i+1)).positiveBranchState :=
  BranchStep.low hwide hv hgap

theorem positive_suffix_branch (P : PolicyJetData m) (hwide : P.a+100*P.q < P.t)
    (hside : P.a+P.t < 2*policyDepth P.policy P.N P.q P.a P.t) :
    BranchStep P.policy P.N P.q P.σ P.positiveBranchState .suffix
      (.D P.a (policyDepth P.policy P.N P.q P.a P.t) (P.i+1)) :=
  BranchStep.suffix hwide hside

theorem positive_high_branch (P : PolicyJetData m) (hwide : P.a+100*P.q < P.t)
    (hside : 2*policyDepth P.policy P.N P.q P.a P.t ≤ P.a+P.t)
    (hleft : P.a₀ = P.a) (hright : P.t₀ = P.t)
    {v : ℕ} (hv : v ∈ Finset.Ioc P.a P.t) (hgap : (P.t:ℝ)-v < P.σ*P.N)
    (hap : P.a ≤ policyDepth P.policy P.N P.q P.a P.t)
    (row : List (Fin (m+3) → Bool) × List (Fin (m+3) → Bool))
    (hrow : row ∈ (P.Q.descendant P.X).occupiedPaths P.ρ
      (policyDepth P.policy P.N P.q P.a P.t-P.a) ×ˢ
        (P.Q.descendant P.Y).occupiedPaths P.ρ (policyDepth P.policy P.N P.q P.a P.t-P.a)) :
    BranchStep P.policy P.N P.q P.σ P.positiveBranchState .high
      (((P.atFrequency v ((Finset.mem_Ioc.mp hv).2.trans P.base_right)).child
        (policyDepth P.policy P.N P.q P.a P.t) hap row hrow).branchState) := by
  change BranchStep P.policy P.N P.q P.σ (.D P.a P.t P.i) .high
    (.H P.a₀ P.t₀ (policyDepth P.policy P.N P.q P.a P.t) v P.i)
  rw [hleft,hright]
  exact BranchStep.high hwide hside hv hgap

theorem directWeight_eq_high_branchExponent (P : PolicyJetData m) (p v : ℕ) (lam σ ε : ℝ)
    (hprofile : P.policy = profileExcess (d := m+3) P.profile P.N) :
    P.directWeight p lam σ ε = ((2:ℝ)^P.N)^(branchExponent P.policy
      (dimensionalBranchReserve (m+3) lam σ) σ ε P.positiveBranchState .high
        (.H P.a P.t p v P.i)) := by
  simp only [directWeight,branchExponent,branchCost,positiveBranchState,BranchState.start,
    reduceCtorEq,ite_false, if_false,hprofile]

theorem low_branchExponent (P : PolicyJetData m) (v : ℕ) (lam σ ε : ℝ) :
    branchExponent P.policy lam σ ε P.positiveBranchState .low (.D P.a v (P.i+1)) = ε := by
  simp only [branchExponent,branchCost,positiveBranchState,BranchState.start,sub_self,
    mul_zero,zero_add,ite_true, if_true]

end PolicyJetData
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PolicyFarSuccessors
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual positive states of a comparable far collision

The two new endpoint cells lie in the same original endpoint cell. Both
retain the descriptor masks and reset only the positive interval and index.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

namespace PolicyJetData
variable {m : ℕ}

theorem farPositiveSuccessor_geometry (P : PolicyJetData m) (a : ℕ) (ha : P.a ≤ a)
    (U : List (Fin (m+3) → Bool)) (hU : U.length = P.a)
    (row : List (Fin (m+3) → Bool) × List (Fin (m+3) → Bool))
    (hr : row ∈ farCellPartners (P.Q.descendant U) P.ρ (a-P.a)) :
    let S := P.farPositiveSuccessor a ha U hU row hr
    125*(((m+3:ℕ):ℝ)+1)*(S.Q.descendant S.X).side ≤
        ‖(S.Q.descendant S.X).center-(S.Q.descendant S.Y).center‖ ∧
      ‖(S.Q.descendant S.X).center-(S.Q.descendant S.Y).center‖ ≤
        2000*(((m+3:ℕ):ℝ)+1)*(S.Q.descendant S.X).side := by
  intro S
  have hgeom := (Finset.mem_filter.mp hr).2
  have hlen := (partner_lengths P a U row hr).1
  have hside : ((P.Q.descendant U).descendant row.1).side =
      (P.Q.descendant U).side/(2:ℝ)^(a-P.a) := by rw [DyadicCube.descendant_side,hlen]
  change 125*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant (U++row.1)).side ≤
      ‖(P.Q.descendant (U++row.1)).center-(P.Q.descendant (U++row.2)).center‖ ∧
    ‖(P.Q.descendant (U++row.1)).center-(P.Q.descendant (U++row.2)).center‖ ≤
      2000*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant (U++row.1)).side
  simp only [DyadicCube.descendant_append,hside]
  rw [norm_sub_rev]
  constructor
  · convert hgeom.1 using 1; ring
  · have hp : 0 < (P.Q.descendant U).side :=
      P.Q.descendant_side_pos (by rw [P.unit]; norm_num) U
    calc
      _ ≤ 1100*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant U).side/(2:ℝ)^(a-P.a) := hgeom.2
      _ = 1100*(((m+3:ℕ):ℝ)+1)*((P.Q.descendant U).side/(2:ℝ)^(a-P.a)) := by ring
      _ ≤ _ := by gcongr; norm_num


theorem farCollisionMaximum_le_positive_successors (P : PolicyJetData m) (a : ℕ) (ha : P.a ≤ a)
    (w₀ : Sphere (m+3)) (M : ℝ)
    (hX : ∀ row, ∀ hr : row ∈ farCellPartners (P.Q.descendant P.X) P.ρ (a-P.a),
      (P.farPositiveSuccessor a ha P.X P.X_length row hr).positiveCount w₀ ≤ M)
    (hY : ∀ row, ∀ hr : row ∈ farCellPartners (P.Q.descendant P.Y) P.ρ (a-P.a),
      (P.farPositiveSuccessor a ha P.Y P.Y_length row hr).positiveCount w₀ ≤ M) :
    farCollisionMaximum w₀ P.Q P.ρ (fun u => P.profile (u/P.N)) P.policy
      P.N P.σ P.J (P.i+1) P.q a P.t P.X P.Y (a-P.a) ≤ ENNReal.ofReal M := by
  let := P.regular.probability
  unfold farCollisionMaximum
  apply Finset.sup_le
  intro z hz
  have hz' := Finset.mem_product.mp hz
  apply max_le
  · rw [← ENNReal.ofReal_toReal (positiveCollisionCount_ne_top w₀ P.Q P.ρ
      (fun u => P.profile (u/P.N)) P.policy P.N P.σ P.J (P.i+1) P.q a P.t
      (P.X++z.1.1) (P.X++z.1.2))]
    exact ENNReal.ofReal_le_ofReal (hX z.1 hz'.1)
  · rw [← ENNReal.ofReal_toReal (positiveCollisionCount_ne_top w₀ P.Q P.ρ
      (fun u => P.profile (u/P.N)) P.policy P.N P.σ P.J (P.i+1) P.q a P.t
      (P.Y++z.2.1) (P.Y++z.2.2))]
    exact ENNReal.ofReal_le_ofReal (hY z.2 hz'.2)

end PolicyJetData
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PolicyEnergy
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual energies represented by scalar branch states

The context fixes the original measure, masks and profile. The constructors
carry the actual positive count or angular envelope, and the positive case
records the cell separation supplied by the far partition.
-/

namespace Falconer
open Set MeasureTheory

namespace PolicyJetData
variable {m : ℕ}

theorem energy_farPositiveSuccessor (P : PolicyJetData m) (K L : ℕ)
    (Ψ : ℝ → ℝ) (w₀ : Sphere (m+3)) (a : ℕ) (ha : P.a ≤ a)
    (U : List (Fin (m+3) → Bool)) (hU : U.length = P.a)
    (row : List (Fin (m+3) → Bool) × List (Fin (m+3) → Bool))
    (hr : row ∈ farCellPartners (P.Q.descendant U) P.ρ (a-P.a)) :
    PolicyEnergy K L Ψ w₀ P.context (.D a P.t (P.i+1))
      ((P.farPositiveSuccessor a ha U hU row hr).positiveCount w₀) := by
  have hg := P.farPositiveSuccessor_geometry a ha U hU row hr
  exact .positive (P.farPositiveSuccessor a ha U hU row hr) rfl rfl hg.1 hg.2


theorem energy_child (P : PolicyJetData m) (K L : ℕ) (Ψ : ℝ → ℝ) (w₀ : Sphere (m+3))
    (p : ℕ) (hap : P.a ≤ p)
    (row : List (Fin (m+3) → Bool) × List (Fin (m+3) → Bool))
    (hr : row ∈ (P.Q.descendant P.X).occupiedPaths P.ρ (p-P.a) ×ˢ
      (P.Q.descendant P.Y).occupiedPaths P.ρ (p-P.a)) :
    PolicyEnergy K L Ψ w₀ P.context (.H P.a₀ P.t₀ p P.t P.i)
      ((P.child p hap row hr).envelope K L Ψ) := .angular (P.child p hap row hr)

theorem energy_positiveSuccessor (P : PolicyJetData m) (K L : ℕ)
    (Ψ : ℝ → ℝ) (w₀ : Sphere (m+3)) (v : ℕ) (hv : v ≤ P.t₀) (i : ℕ)
    (lower : 125*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side ≤
      ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖)
    (upper : ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ ≤
      2000*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side) :
    PolicyEnergy K L Ψ w₀ P.context (.D P.a v i)
      ((P.positiveSuccessor v hv i).positiveCount w₀) :=
  .positive (P.positiveSuccessor v hv i) rfl rfl lower upper

end PolicyJetData
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PolicyEnergySteps
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Applying the analytic recurrences to actual branch energies -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (BranchState BranchStep BranchLabel branchExponent policyDepth)

namespace PolicyJetData
variable {m : ℕ}

theorem positive_energy_step (P : PolicyJetData m) {K L N₀ : ℕ} {ε T : ℝ}
    {Ψ : ℝ → ℝ} (w₀ : Sphere (m+3))
    (hrec : PolicyRecursionBounds m K L P.J P.lam P.σ ε T P.Z N₀ Ψ)
    (hN : N₀ ≤ P.N) (hi : P.i+1 ≤ P.J)
    (hprofile : P.policy = profileExcess (d := m+3) P.profile P.N)
    (hleft : P.a₀ = P.a) (hright : P.t₀ = P.t)
    (hwide : P.a+100*P.q < P.t) (hq : P.σ*(P.N:ℝ) ≤ P.q)
    (hcover : ∀ b ∈ P.list, ∀ w : Sphere (m+3), ∃ c ∈ P.masks b,
      dist w c ≤ descriptorMaskRadius P.N P.σ b/2)
    (hlo : 125*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side ≤
      ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖)
    (hhi : ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ ≤
      2000*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side)
    (M : ℝ) (hM : 0 ≤ M) (hfloor : ((2:ℝ)^P.N)^(4*(((m+3:ℕ):ℝ)+1)*P.lam+ε) ≤ M)
    (hchildren : P.ChildrenBound K L Ψ w₀ P.positiveBranchState ε M) :
    P.positiveCount w₀ ≤ 3*M+((2:ℝ)^P.N)^(-T) := by
  by_cases hside : 2*policyDepth P.policy P.N P.q P.a P.t ≤ P.a+P.t
  · apply hrec.positive P rfl rfl rfl rfl hN hi hleft hright hwide hq hside hcover
      hlo hhi w₀ M hM hfloor
    · intro v hv hgap
      have hb := hchildren _ _ (P.positive_low_branch hwide hv hgap) _
        (P.energy_positiveSuccessor K L Ψ w₀ v
          ((Finset.mem_Ioc.mp hv).2.trans P.base_right) (P.i+1) hlo hhi)
      change ((2:ℝ)^P.N)^(branchExponent P.policy
        (dimensionalBranchReserve (m+3) P.lam P.σ) P.σ ε P.positiveBranchState .low
        (.D P.a v (P.i+1)))*_ ≤ M at hb
      rw [P.low_branchExponent] at hb
      exact hb
    · intro v hv hgap p hp hap row hrow
      subst p
      have hb := hchildren _ _ (P.positive_high_branch hwide hside hleft hright hv hgap hap row hrow) _
        (PolicyEnergy.angular
          ((P.atFrequency v ((Finset.mem_Ioc.mp hv).2.trans P.base_right)).child
            (policyDepth P.policy P.N P.q P.a P.t) hap row hrow))
      change ((2:ℝ)^P.N)^(branchExponent P.policy
        (dimensionalBranchReserve (m+3) P.lam P.σ) P.σ ε P.positiveBranchState .high
        (.H P.a₀ P.t₀ (policyDepth P.policy P.N P.q P.a P.t) v P.i))*_ ≤ M at hb
      have he : branchExponent P.policy (dimensionalBranchReserve (m+3) P.lam P.σ) P.σ ε
          P.positiveBranchState .high (.H P.a₀ P.t₀ (policyDepth P.policy P.N P.q P.a P.t) v P.i) =
          branchExponent P.policy (dimensionalBranchReserve (m+3) P.lam P.σ) P.σ ε
          P.positiveBranchState .high (.H P.a P.t (policyDepth P.policy P.N P.q P.a P.t) v P.i) := by
        rw [hleft,hright]
      rw [he,← P.directWeight_eq_high_branchExponent _ _ _ _ _ hprofile] at hb
      exact hb
  · have hp := (PlanarFalconer.policyDepth_interior P.policy P.q_pos
      (PlanarFalconer.policyBlocks_nonempty P.q_pos (P.base_right.trans P.base_N) hwide)).2
    have hs := P.positive_suffix_branch hwide (by omega)
    have hb := hchildren _ _ hs _
      (P.energy_positiveSuccessor K L Ψ w₀ (policyDepth P.policy P.N P.q P.a P.t)
        ((hp.trans (Nat.sub_le _ _)).trans P.base_right) (P.i+1) hlo hhi)
    simp only [positiveBranchState] at hb
    rw [← P.suffixWeight_eq_branchExponent _ _ _ _ hprofile] at hb
    have he := hrec.suffix P rfl rfl rfl hN (by omega) hwide (by omega) hlo w₀
    have hstep : P.positiveCount w₀ ≤ M := he.trans hb
    have herr : 0 ≤ ((2:ℝ)^P.N)^(-T) := by positivity
    linarith


theorem angular_energy_step (P : PolicyJetData m) {K L N₀ : ℕ} {ε T : ℝ}
    {Ψ : ℝ → ℝ} (w₀ : Sphere (m+3))
    (hrec : PolicyRecursionBounds m K L P.J P.lam P.σ ε T P.Z N₀ Ψ)
    (hN : N₀ ≤ P.N) (hi : P.i+1 ≤ P.J) (hσ : 0 < P.σ) (hZ : 1 ≤ P.Z)
    (hprofile : P.policy = profileExcess (d := m+3) P.profile P.N)
    (hbase : (P.t₀:ℝ) ≤ P.t+P.σ*P.N)
    (hwide : P.a+100*P.q < P.t) (hq : P.σ*(P.N:ℝ) ≤ P.q)
    (hceil : ⌈10*P.σ*(P.N:ℝ)⌉₊ < P.q) (hq10 : 10*P.σ*(P.N:ℝ) ≤ P.q)
    (M : ℝ) (hM : 0 ≤ M)
    (hchildren : P.ChildrenBound K L Ψ w₀ P.branchState ε M) :
    P.envelope K L Ψ ≤ 3*M+((2:ℝ)^P.N)^(-T) := by
  by_cases hfar : P.a < P.splitDepth
  · have hnear : ∀ row, ∀ hrow : row ∈
        (P.Q.descendant P.X).occupiedPaths P.ρ (P.splitDepth-P.a) ×ˢ
          (P.Q.descendant P.Y).occupiedPaths P.ρ (P.splitDepth-P.a),
        P.farWeight P.splitDepth P.lam P.σ ε *
          (P.child P.splitDepth hfar.le row hrow).envelope K L Ψ ≤ M := by
      intro row hrow
      rw [P.nearWeight_eq_branchExponent _ _ _ hprofile]
      exact hchildren _ _ (P.near_branch hwide hfar) _
        (P.energy_child K L Ψ w₀ P.splitDepth hfar.le row hrow)
    have hcollisions : ∀ b ∈ Finset.Icc (P.a+9) (P.splitDepth+6),
        ENNReal.ofReal (P.farWeight b P.lam P.σ ε)*
          farCollisionMaximum w₀ P.Q P.ρ (fun t => P.profile (t/P.N))
            P.policy P.N P.σ P.J (P.i+1) P.q b P.t P.X P.Y (b-P.a) ≤ ENNReal.ofReal M := by
      intro b hb
      have hab : P.a ≤ b := by have := (Finset.mem_Icc.mp hb).1; omega
      have hw : 0 < P.farWeight b P.lam P.σ ε := by unfold farWeight; positivity
      have hends (U : List (Fin (m+3) → Bool)) (hU : U.length = P.a)
          (row : List (Fin (m+3) → Bool) × List (Fin (m+3) → Bool))
          (hr : row ∈ farCellPartners (P.Q.descendant U) P.ρ (b-P.a)) :
          (P.farPositiveSuccessor b hab U hU row hr).positiveCount w₀ ≤
            M/P.farWeight b P.lam P.σ ε := by
        apply (le_div_iff₀ hw).mpr
        have he := hchildren _ _ (P.far_branch hwide hfar hb) _
          (P.energy_farPositiveSuccessor K L Ψ w₀ b hab U hU row hr)
        rw [← P.farWeight_eq_branchExponent _ _ _ _ hprofile] at he
        simpa only [mul_comm] using he
      have hmax := P.farCollisionMaximum_le_positive_successors b hab w₀
        (M/P.farWeight b P.lam P.σ ε) (hends P.X P.X_length) (hends P.Y P.Y_length)
      calc
        _ ≤ ENNReal.ofReal (P.farWeight b P.lam P.σ ε)*
            ENNReal.ofReal (M/P.farWeight b P.lam P.σ ε) := mul_le_mul' le_rfl hmax
        _ = ENNReal.ofReal M := by
          rw [← ENNReal.ofReal_mul hw.le,mul_div_cancel₀ _ hw.ne']
    have he := hrec.far P rfl rfl hN hfar hZ w₀ M hM hnear hcollisions
    linarith
  · obtain ⟨d,hd⟩ := PlanarFalconer.actual_direct_policy_witness P.policy hσ.le P.q_pos
      hceil hq hq10 hbase hwide (Nat.le_of_not_gt hfar)
    have hchild : ∀ row, ∀ hrow : row ∈
        (P.Q.descendant P.X).occupiedPaths P.ρ ((P.directGeometry d hd).p-P.a) ×ˢ
          (P.Q.descendant P.Y).occupiedPaths P.ρ ((P.directGeometry d hd).p-P.a),
        P.directWeight (P.directGeometry d hd).p P.lam P.σ ε *
          (P.child (P.directGeometry d hd).p (P.directGeometry d hd).ap row hrow).envelope K L Ψ ≤ M := by
      intro row hrow
      rw [P.directWeight_eq_branchExponent _ _ _ _ hprofile]
      exact hchildren _ _ (P.direct_branch hwide hd) _
        (P.energy_child K L Ψ w₀ (P.directGeometry d hd).p (P.directGeometry d hd).ap row hrow)
    have he := hrec.graph P rfl rfl rfl rfl hN hi (P.directGeometry d hd) M hM hchild
    linarith

end PolicyJetData
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_BranchRecursionOrder
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem BranchStep.width_decreases {A : ℕ → ℝ} {N q : ℕ} {sig : ℝ}
    (hN : 0 < N) (hq : 0 < q) (hsig : 0 < sig)
    {s u : BranchState} {label : BranchLabel} (h : BranchStep A N q sig s label u)
    (hs : s.Valid N sig) (hu : u.Valid N sig) :
    u.finish-u.start < s.finish-s.start := by
  have hn := h.nested hq hs
  have hsd := BranchState.valid_depths hs
  have hud := BranchState.valid_depths hu
  have hstrict : s.start < u.start ∨ u.finish < s.finish := by
    cases h with
    | suffix hw _ =>
      have hp := policyDepth_interior A hq (policyBlocks_nonempty hq hs.2 hw)
      exact Or.inr (by dsimp only [BranchState.finish]; omega)
    | low _ _ hg =>
      have hpos : 0 < sig*(N:ℝ) := mul_pos hsig (Nat.cast_pos.mpr hN)
      apply Or.inr
      apply (Nat.cast_lt (α := ℝ)).mp
      dsimp only [BranchState.finish]
      linarith
    | high hw _ _ _ =>
      have hp := policyDepth_interior A hq (policyBlocks_nonempty hq hs.2 hw)
      exact Or.inl (by dsimp only [BranchState.start]; omega)
    | near _ hp => exact Or.inl hp
    | far _ _ hm =>
      have hm := Finset.mem_Icc.mp hm
      exact Or.inl (by dsimp only [BranchState.start]; omega)
    | direct _ he => exact Or.inl he.anchor_gt
  omega

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ReachedBranchWeights
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
namespace PolicyBranch
variable {A : ℕ → ℝ} {N q n : ℕ} {sig : ℝ}

theorem weight_pos (b : PolicyBranch A N q sig n) (lam eps : ℝ) : 0 < b.weight lam eps := by
  unfold weight
  positivity

theorem exponentSum_extend (b : PolicyBranch A N q sig n) (lam eps : ℝ)
    {u : BranchState} {l : BranchLabel} (hu : u.Valid N sig)
    (hstep : BranchStep A N q sig (b.state n) l u) :
    (b.extend hu hstep).exponentSum lam eps = b.exponentSum lam eps+
      branchExponent A lam sig eps (b.state n) l u := by
  unfold exponentSum
  rw [Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hj := Finset.mem_range.mp hj
    rw [b.extend_state_le hu hstep hj.le,b.extend_label_lt hu hstep hj,
      b.extend_state_le hu hstep (by omega : j+1 ≤ n)]
  · rw [b.extend_state_le hu hstep le_rfl,b.extend_last_label,b.extend_last_state]

theorem weight_extend (b : PolicyBranch A N q sig n) (lam eps : ℝ)
    {u : BranchState} {l : BranchLabel} (hu : u.Valid N sig)
    (hstep : BranchStep A N q sig (b.state n) l u) :
    (b.extend hu hstep).weight lam eps = b.weight lam eps*
      ((2:ℝ)^N)^(branchExponent A lam sig eps (b.state n) l u) := by
  unfold weight
  rw [exponentSum_extend,Real.rpow_add (by positivity)]

theorem weight_zero (b : PolicyBranch A N q sig 0) (lam eps : ℝ) : b.weight lam eps = 1 := by
  simp [weight,exponentSum]

end PolicyBranch

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_DimensionalBranchBounds
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Branch weights for the ambient-dimensional profile

The excess profile is d-Lipschitz. These estimates retain that factor in
both the terminal potential payment and the accumulated error exponent.
-/

namespace Falconer
open PlanarFalconer

theorem profileExcess_dimensional_lipschitz {d N : ℕ} {Q : DyadicCube d}
    {ρ : MeasureTheory.Measure (Space d)} {profile : ℝ → ℝ} {s lam : ℝ}
    (hreg : Regularization.RegularizedProfileData Q ρ N s lam profile) (hN : 0 < N) :
    DimensionalProfileLipschitz d (profileExcess (d := d) profile N) N := by
  intro i hi j hj
  exact profileExcess_lipschitz Q ρ hreg hN i j hi hj

theorem dimensional_potential_le_final_start {A : ℕ → ℝ} {d N a t f Q : ℕ}
    (hN : 0 < N) (hA : DimensionalProfileLipschitz d A N)
    (hQ : 0 < Q) (hw : a+Q ≤ t) (ht : t ≤ N) (haf : a ≤ f) (hft : f ≤ t) :
    potential A a t Q ≤ 2*A f+2*d*(Q:ℝ)/N := by
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hb := potential_near_final A hQ hw haf hft (e := (d:ℝ)*(Q:ℝ)/N) ?_
  · simpa only [mul_div_assoc,mul_assoc] using hb
  intro j _ hjt hjf hfj
  have hd : |(j:ℝ)-f| ≤ (Q:ℝ) := by
    have hjR : (j:ℝ) ≤ (f:ℝ)+Q := by exact_mod_cast hjf
    have hfR : (f:ℝ) ≤ (j:ℝ)+Q := by exact_mod_cast hfj
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hh := (hA j (hjt.trans ht) f (hft.trans ht)).trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg d)) hNR.le)
  have hh' := (le_abs_self (A j-A f)).trans hh
  linarith

theorem _root_.OAI.PlanarFalconer.PolicyBranch.dimensional_costs_le_final_start {d N q n : ℕ} {A : ℕ → ℝ} {sig : ℝ}
    (b : PolicyBranch A N q sig n) (hN : 0 < N) (hq : 0 < q)
    (hslack : sig*(N:ℝ) ≤ q) (hA : DimensionalProfileLipschitz d A N)
    (hinit : (b.state 0).start+10*q ≤ (b.state 0).finish) :
    ∑ j ∈ Finset.range n, branchCost A (b.state j) (b.label j) (b.state (j+1)) ≤
      2*A (b.state n).start+20*d*(q:ℝ)/N-potential A (b.state 0).start (b.state 0).finish (10*q) := by
  have hQ : 0 < 10*q := by omega
  have hfinal := BranchState.valid_depths (b.valid n le_rfl)
  by_cases hw : (b.state n).start+10*q ≤ (b.state n).finish
  · have hc := b.costs_le_potential hq hslack hw
    have hf := dimensional_potential_le_final_start hN hA hQ hw hfinal.2 (le_refl _) hfinal.1
    norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hf
    linear_combination hc+hf
  · cases n with
    | zero => exact (hw hinit).elim
    | succ n =>
      have hs := b.step n (by omega)
      have hn := hs.nested hq (b.valid n (by omega))
      have hp := hs.nonterminal
      have hpwide : (b.state n).start+10*q ≤ (b.state n).finish := by omega
      have hd := BranchState.valid_depths (b.valid n (by omega))
      have hc := (b.initialSegment n (by omega)).costs_le_potential hq hslack hpwide
      dsimp only [PlanarFalconer.PolicyBranch.initialSegment] at hc
      have hz := hs.short_cost_zero hq (b.valid n (by omega)) hslack (by omega)
      have hf := dimensional_potential_le_final_start hN hA hQ hpwide hd.2 hn.1 (hfinal.1.trans hn.2)
      norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hf
      rw [Finset.sum_range_succ,hz,add_zero]
      linear_combination hc+hf

theorem DimensionalProfileLipschitz.increment_le {d N i j : ℕ} {A : ℕ → ℝ}
    (hA : DimensionalProfileLipschitz d A N) (hN : 0 < N) (hi : i ≤ N) (hj : j ≤ N) :
    |A i-A j| ≤ d := by
  apply (hA i hi j hj).trans
  apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
  apply abs_le.mpr
  have hi' : (i:ℝ) ≤ N := Nat.cast_le.mpr hi
  have hj' : (j:ℝ) ≤ N := Nat.cast_le.mpr hj
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) i,Nat.cast_nonneg (α := ℝ) j]

theorem DimensionalProfileLipschitz.minimum_cost_le {d N a t i : ℕ} {A : ℕ → ℝ}
    (hA : DimensionalProfileLipschitz d A N) (hN : 0 < N)
    (hat : a ≤ t) (ht : t ≤ N) (hi : i ≤ N) : A i-intervalMin A a t ≤ d := by
  obtain ⟨j,_,hjt,hmin⟩ := intervalMin_attained A hat
  rw [hmin]
  exact (le_abs_self _).trans (hA.increment_le hN hi (hjt.trans ht))

theorem _root_.OAI.PlanarFalconer.BranchStep.dimensional_cost_le {A : ℕ → ℝ} {d N q : ℕ} {sig : ℝ}
    (hA : DimensionalProfileLipschitz d A N) (hN : 0 < N) (hq : 0 < q)
    {s u : BranchState} {l : BranchLabel} (h : BranchStep A N q sig s l u)
    (hs : s.Valid N sig) (hu : u.Valid N sig) : branchCost A s l u ≤ d := by
  have hn := h.nested hq hs
  have hsd := BranchState.valid_depths hs
  have hud := BranchState.valid_depths hu
  cases h <;> simp only [branchCost]
  · exact hA.minimum_cost_le hN hn.2 hsd.2 (hud.2.trans (le_refl _))
  · norm_num
  · exact hA.minimum_cost_le hN hn.1 (hud.1.trans hud.2) (hud.1.trans hud.2)
  · norm_num
  · norm_num
  · exact hA.minimum_cost_le hN hn.1 (hud.1.trans hud.2) (hud.1.trans hud.2)

theorem _root_.OAI.PlanarFalconer.BranchStep.dimensional_exponent_le {A : ℕ → ℝ} {d N q : ℕ} {lam sig eps : ℝ}
    (hA : DimensionalProfileLipschitz d A N) (hN : 0 < N) (hq : 0 < q)
    (hloss : 4000*(lam+sig) ≤ 1)
    {s u : BranchState} {l : BranchLabel} (h : BranchStep A N q sig s l u)
    (hs : s.Valid N sig) (hu : u.Valid N sig) :
    branchExponent A lam sig eps s l u ≤ 3*(d:ℝ)+1+eps := by
  have hc := h.dimensional_cost_le hA hN hq hs hu
  have hsd := BranchState.valid_depths hs
  have hud := BranchState.valid_depths hu
  have hi := abs_le.mp (hA.increment_le hN (hud.1.trans hud.2) (hsd.1.trans hsd.2))
  unfold branchExponent
  split_ifs <;> linarith

theorem _root_.OAI.PlanarFalconer.PolicyBranch.dimensional_ancestor_exponent_bound {A : ℕ → ℝ} {d N q n : ℕ} {lam sig eps : ℝ}
    (b : PolicyBranch A N q sig n) (hA : DimensionalProfileLipschitz d A N)
    (hN : 0 < N) (hq : 0 < q) (hloss : 4000*(lam+sig) ≤ 1) :
    (∑ j ∈ Finset.range n, branchExponent A lam sig eps (b.state j) (b.label j) (b.state (j+1))) ≤
      (n:ℝ)*(3*(d:ℝ)+1+eps) := by
  calc
    _ ≤ ∑ _j ∈ Finset.range n, (3*(d:ℝ)+1+eps) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj := Finset.mem_range.mp hj
      exact (b.step j hj).dimensional_exponent_le hA hN hq hloss (b.valid j hj.le)
        (b.valid (j+1) (by omega))
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]

theorem dimensional_source_branch_exponent {A : ℕ → ℝ} {d N n : ℕ} {lam sig kap eta : ℝ}
    (hN : 0 < N) (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (heta : 0 < eta) (hceil : ⌈10*sig*(N:ℝ)⌉₊ < sourcePolicyBlock N kap)
    (hslack : sig*(N:ℝ) ≤ sourcePolicyBlock N kap)
    (hqratio : (sourcePolicyBlock N kap:ℝ)/(N:ℝ) ≤ 2*kap)
    (hA : DimensionalProfileLipschitz d A N)
    (b : PolicyBranch A N (sourcePolicyBlock N kap) sig n)
    (hinit : (b.state 0).start+10*sourcePolicyBlock N kap ≤ (b.state 0).finish) :
    let eps := eta/(2*(1+20/kap+1/sig))
    (∑ j ∈ Finset.range n, branchExponent A lam sig eps (b.state j) (b.label j) (b.state (j+1))) +
      (200*d*(sourcePolicyBlock N kap:ℝ)/N+12*lam+eta/2) ≤
      2*A (b.state 0).start-potential A (b.state 0).start (b.state 0).finish
        (10*sourcePolicyBlock N kap)+500*d*kap+10^6*(lam+sig)/kap+eta := by
  dsimp only
  have hq := sourcePolicyBlock_pos hN hkap
  have hc := b.dimensional_costs_le_final_start hN hq hslack hA hinit
  have hb := source_branch_count_bounds hN hsig hkap hkap1 hceil b
  let D : ℝ := 1+20/kap+1/sig
  have hD : 0 < D := by dsimp [D]; positivity
  have heps : 0 ≤ eta/(2*D) := by positivity
  have htime : (n:ℝ)*(eta/(2*D)) ≤ eta/2 := by
    have hn : (n:ℝ) ≤ D := by dsimp [D]; linarith [hb.2.2]
    calc
      _ ≤ D*(eta/(2*D)) := mul_le_mul_of_nonneg_right hn heps
      _ = eta/2 := by field_simp
  have hloss : (branchNonlowCount b.label n:ℝ)*(4000*(lam+sig)) ≤ 80000*(lam+sig)/kap := by
    calc
      _ ≤ (20/kap)*(4000*(lam+sig)) := mul_le_mul_of_nonneg_right hb.1 (by positivity)
      _ = _ := by ring
  have hlamK : lam ≤ (lam+sig)/kap := by
    apply (le_div_iff₀ hkap).mpr
    have hh := mul_le_mul_of_nonneg_left hkap1 hlam
    linarith
  have hbudget : 0 ≤ (lam+sig)/kap := by positivity
  have hqrd := mul_le_mul_of_nonneg_left hqratio (Nat.cast_nonneg (α := ℝ) d)
  rw [branch_exponent_sum]
  dsimp only [D] at htime
  simp only [mul_div_assoc] at hc hloss ⊢
  nlinarith

theorem uniform_dimensional_source_branch_exponent {d : ℕ} {lam sig kap eta : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (hgap : sig < kap/1000) (heta : 0 < eta) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ A : ℕ → ℝ,
      DimensionalProfileLipschitz d A N → ∀ n : ℕ,
      ∀ b : PolicyBranch A N (sourcePolicyBlock N kap) sig n,
      (b.state 0).start+10*sourcePolicyBlock N kap ≤ (b.state 0).finish →
      (∑ j ∈ Finset.range n, branchExponent A lam sig (eta/(2*(1+20/kap+1/sig)))
        (b.state j) (b.label j) (b.state (j+1))) +
        (200*d*(sourcePolicyBlock N kap:ℝ)/N+12*lam+eta/2) ≤
      2*A (b.state 0).start-potential A (b.state 0).start (b.state 0).finish
        (10*sourcePolicyBlock N kap)+500*d*kap+10^6*(lam+sig)/kap+eta := by
  obtain ⟨N₁,hN₁,h₁⟩ := uniform_source_ceiling_slack hsig hgap
  obtain ⟨N₂,hN₂⟩ := exists_nat_gt (1/kap)
  refine ⟨max N₁ N₂,by omega,?_⟩
  intro N hN A hA n b hi
  have hNp : 0 < N := by omega
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hNp
  have hkn : 1 < kap*(N:ℝ) := by
    have hh := (div_lt_iff₀ hkap).mp (hN₂.trans_le (Nat.cast_le.mpr (show N₂ ≤ N by omega)))
    linarith
  have hq : (sourcePolicyBlock N kap:ℝ) < kap*N+1 :=
    Nat.ceil_lt_add_one (mul_nonneg hkap.le hNR.le)
  have hqr : (sourcePolicyBlock N kap:ℝ)/(N:ℝ) ≤ 2*kap :=
    (div_le_iff₀ hNR).mpr (by linarith)
  exact dimensional_source_branch_exponent hNp hlam hsig hkap hkap1 heta
    (h₁ N (by omega)).1 (h₁ N (by omega)).2.2 hqr hA b hi

theorem dimensional_source_error_exponent {d : ℕ} {sig kap T eps n : ℝ}
    (hn : 0 ≤ n)
    (hdepth : n ≤ 20/kap+1/sig) (heps : eps ≤ 1)
    (hT : (20/kap+1/sig)*(3*(d:ℝ)+2)+10 < T) :
    -T+n*(3*(d:ℝ)+1+eps) < -10 := by
  have hstep : n*(3*(d:ℝ)+1+eps) ≤ n*(3*(d:ℝ)+2) := by nlinarith
  have hbound := mul_le_mul_of_nonneg_right hdepth
    (show 0 ≤ 3*(d:ℝ)+2 by positivity)
  linarith

theorem dimensional_uniform_source_error_branch {d : ℕ} {lam sig kap T eps : ℝ}
    (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1) (hgap : sig < kap/1000)
    (hloss : 4000*(lam+sig) ≤ 1) (heps : eps ≤ 1)
    (hT : (20/kap+1/sig)*(3*(d:ℝ)+2)+10 < T) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ A : ℕ → ℝ,
      DimensionalProfileLipschitz d A N → ∀ n : ℕ,
      ∀ b : PolicyBranch A N (sourcePolicyBlock N kap) sig n,
      (b.state 0).index = 0 →
      ((2:ℝ)^N)^(-T+(∑ j ∈ Finset.range n,
        branchExponent A lam sig eps (b.state j) (b.label j) (b.state (j+1)))) ≤
      ((2:ℝ)^N)^(-10:ℝ) := by
  obtain ⟨N₀,hN₀,h₀⟩ := uniform_source_branch_depth hsig hkap hkap1 hgap
  refine ⟨N₀,hN₀,?_⟩
  intro N hN A hA n b hi
  have hNp : 0 < N := hN₀.trans_le hN
  have hc := b.dimensional_ancestor_exponent_bound (eps := eps) hA hNp (sourcePolicyBlock_pos hNp hkap) hloss
  have hd := (h₀ N hN A n b hi).2.2.1
  have he := dimensional_source_error_exponent (Nat.cast_nonneg n) hd heps hT
  apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
  linarith

theorem dimensional_uniform_source_weighted_terminal {d : ℕ} {lam sig kap eta : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (hgap : sig < kap/1000) (heta : 0 < eta) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ A : ℕ → ℝ,
      DimensionalProfileLipschitz d A N → ∀ n : ℕ,
      ∀ b : PolicyBranch A N (sourcePolicyBlock N kap) sig n,
      (b.state 0).start+10*sourcePolicyBlock N kap ≤ (b.state 0).finish →
      b.weight lam (eta/(2*(1+20/kap+1/sig))) *
        ((2:ℝ)^N)^(200*d*(sourcePolicyBlock N kap:ℝ)/N+12*lam+eta/2) ≤
      ((2:ℝ)^N)^(2*A (b.state 0).start-potential A (b.state 0).start (b.state 0).finish
        (10*sourcePolicyBlock N kap)+500*d*kap+10^6*(lam+sig)/kap+eta) := by
  obtain ⟨N₀,hN₀,h₀⟩ := uniform_dimensional_source_branch_exponent hlam hsig hkap hkap1 hgap heta
  refine ⟨N₀,hN₀,?_⟩
  intro N hN A hA n b hi
  rw [PolicyBranch.weight,← Real.rpow_add (by positivity : 0 < (2:ℝ)^N)]
  exact Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (h₀ N hN A hA n b hi)

theorem dimensional_uniform_source_weighted_error {d : ℕ} {lam sig kap T eps : ℝ}
    (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1) (hgap : sig < kap/1000)
    (hloss : 4000*(lam+sig) ≤ 1) (heps : eps ≤ 1)
    (hT : (20/kap+1/sig)*(3*(d:ℝ)+2)+10 < T) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ A : ℕ → ℝ,
      DimensionalProfileLipschitz d A N → ∀ n : ℕ,
      ∀ b : PolicyBranch A N (sourcePolicyBlock N kap) sig n,
      (b.state 0).index = 0 →
      b.weight lam eps*((2:ℝ)^N)^(-T) ≤ ((2:ℝ)^N)^(-10:ℝ) := by
  obtain ⟨N₀,hN₀,h₀⟩ := dimensional_uniform_source_error_branch hsig hkap hkap1 hgap hloss heps hT
  refine ⟨N₀,hN₀,?_⟩
  intro N hN A hA n b hi
  rw [PolicyBranch.weight,← Real.rpow_add (by positivity : 0 < (2:ℝ)^N),add_comm]
  exact h₀ N hN A hA n b hi

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PolicyTerminal
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform stopping bound for actual angular policy states -/

namespace Falconer
open Set MeasureTheory

theorem eventual_policy_angular_terminal (m K : ℕ) {ε W : ℝ}
    (hε : 0 < ε) (hW : 0 ≤ W) (Ψ : ℝ → ℝ)
    (hΨW : ∀ u, Ψ u ≤ W) (hsupp : ∀ u, 4 < u → Ψ u = 0) :
    ∃ N₀ : ℕ, ∀ (P : PolicyJetData m) (L : ℕ), N₀ ≤ P.N →
      P.a ≤ P.N → P.t ≤ P.a+100*P.q → 1 ≤ P.Z →
      P.envelope K L Ψ ≤
        ((2:ℝ)^P.N)^(100*((m+3:ℕ):ℝ)*P.q/P.N+4*(((m+3:ℕ):ℝ)+1)*P.lam+ε) := by
  let C : ℝ := 4*W*((descriptorJetBound (m+3) K)^K)^4*
    (sphereMeasure (m+3)).real univ^2
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hε C
  refine ⟨N₀,?_⟩
  intro P L hN ha ht hZ
  have hz : P.Z⁻¹ ≤ 1 := (inv_le_one₀ P.Z_pos).mpr hZ
  have hJ : 0 ≤ (descriptorJetBound (m+3) K)^K :=
    pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) K
  have hpower : ((descriptorJetBound (m+3) K)^K*P.Z⁻¹)^4 ≤
      ((descriptorJetBound (m+3) K)^K)^4 := by
    apply pow_le_pow_left₀ (mul_nonneg hJ (inv_nonneg.mpr P.Z_pos.le))
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hz hJ
  have hcost : 4*W*((descriptorJetBound (m+3) K)^K*P.Z⁻¹)^4*
      (sphereMeasure (m+3)).real univ^2 ≤ C := by
    dsimp [C]
    gcongr
  have htR : (P.t:ℝ) ≤ (P.a:ℝ)+100*P.q := by exact_mod_cast ht
  have hterm := profile_jetState_terminal (K := K) (L := L) (D := 1) P.list
    P.Q P.ρ P.regular P.N_pos P.σ P.J P.i P.masks P.separated P.Z_pos ha
    P.X P.Y P.X_length P.Y_length (P.t:ℝ) htR Ψ hW hΨW hsupp
  apply hterm.trans
  calc
    _ ≤ C*((2:ℝ)^P.N)^(100*((m+3:ℕ):ℝ)*P.q/P.N+4*(((m+3:ℕ):ℝ)+1)*P.lam) :=
      mul_le_mul_of_nonneg_right hcost (by positivity)
    _ ≤ ((2:ℝ)^P.N)^ε*
        ((2:ℝ)^P.N)^(100*((m+3:ℕ):ℝ)*P.q/P.N+4*(((m+3:ℕ):ℝ)+1)*P.lam) :=
      mul_le_mul_of_nonneg_right (hN₀ P.N hN) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity : 0 < (2:ℝ)^P.N)]; congr 1; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_WeightedBranchInduction
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem weighted_branch_energy_induction (A : ℕ → ℝ) (N q D : ℕ)
    (sig lam eps C terminal floor error L E : ℝ) (root : BranchState)
    (energies : BranchState → ℝ → Prop)
    (hN : 0 < N) (hq : 0 < q) (hsig : 0 < sig)
    (hC : 1 ≤ C) (hL : 0 ≤ L) (hE : 0 ≤ E)
    (hvalid : ∀ s u l, s.Valid N sig → BranchStep A N q sig s l u → u.Valid N sig)
    (hdepth : ∀ n, ∀ b : PolicyBranch A N q sig n, b.state 0 = root → n ≤ D)
    (hterminal : ∀ s, s.Valid N sig → s.finish ≤ s.start+100*q →
      ∀ x, energies s x → x ≤ terminal)
    (hreduction : ∀ s, s.Valid N sig →
      (∃ n, ∃ b : PolicyBranch A N q sig n, b.state 0 = root ∧ b.state n = s) →
      s.start+100*q < s.finish →
      ∀ M : ℝ, 0 ≤ M → floor ≤ M →
      (∀ u l, BranchStep A N q sig s l u → ∀ x, energies u x →
        ((2:ℝ)^N)^(branchExponent A lam sig eps s l u)*x ≤ M) →
      ∀ x, energies s x → x ≤ C*M+error)
    (htermWeight : ∀ n, ∀ b : PolicyBranch A N q sig n, b.state 0 = root →
      b.weight lam eps*terminal ≤ L)
    (hfloorWeight : ∀ n, ∀ b : PolicyBranch A N q sig n, b.state 0 = root →
      b.weight lam eps*floor ≤ L)
    (herrorWeight : ∀ n, ∀ b : PolicyBranch A N q sig n, b.state 0 = root →
      b.weight lam eps*error ≤ E) :
    ∀ n, ∀ b : PolicyBranch A N q sig n, b.state 0 = root →
      ∀ x, energies (b.state n) x →
      b.weight lam eps*x ≤ (C+1)^(D-n+1)*(L+E) := by
  have haux : ∀ s : BranchState, ∀ n, ∀ b : PolicyBranch A N q sig n,
      b.state 0 = root → b.state n = s → ∀ x, energies s x →
      b.weight lam eps*x ≤ (C+1)^(D-n+1)*(L+E) := by
    intro s
    induction s using (measure (fun s : BranchState => s.finish-s.start)).wf.induction with
    | h s ih =>
      intro n b hroot hlast x hx
      have hs : s.Valid N sig := hlast ▸ b.valid n le_rfl
      have hW := b.weight_pos lam eps
      have hsum : 0 ≤ L+E := add_nonneg hL hE
      have hpow : 1 ≤ (C+1)^(D-n) := one_le_pow₀ (by linarith)
      let H := (C+1)^(D-n)*(L+E)
      have hLH : L ≤ H := by dsimp only [H]; nlinarith
      have hEH : E ≤ H := by dsimp only [H]; nlinarith
      have hH : 0 ≤ H := hL.trans hLH
      have hHlast : H ≤ (C+1)^(D-n+1)*(L+E) := by
        rw [pow_succ]
        change H ≤ (C+1)^(D-n)*(C+1)*(L+E)
        nlinarith
      by_cases hw : s.finish ≤ s.start+100*q
      · have ht := hterminal s hs hw x hx
        exact ((mul_le_mul_of_nonneg_left ht hW.le).trans (htermWeight n b hroot)).trans
          (hLH.trans hHlast)
      · have hfloor : floor ≤ H/b.weight lam eps := by
          apply (le_div_iff₀ hW).mpr
          simpa only [mul_comm] using (hfloorWeight n b hroot).trans hLH
        have hchildren : ∀ u l, BranchStep A N q sig s l u → ∀ y, energies u y →
            ((2:ℝ)^N)^(branchExponent A lam sig eps s l u)*y ≤ H/b.weight lam eps := by
          intro u l hstep y hy
          have hu := hvalid s u l hs hstep
          have hstep' : BranchStep A N q sig (b.state n) l u := hlast ▸ hstep
          let b' := b.extend hu hstep'
          have hroot' : b'.state 0 = root := by
            change (b.extend hu hstep').state 0 = root
            rw [b.extend_state_le hu hstep' (Nat.zero_le n),hroot]
          have hlast' : b'.state (n+1) = u := b.extend_last_state hu hstep'
          have hnd := hdepth (n+1) b' hroot'
          have hi := ih u (hstep.width_decreases hN hq hsig hs hu) (n+1) b' hroot' hlast' y hy
          have harith : D-(n+1)+1 = D-n := by omega
          rw [harith] at hi
          change b'.weight lam eps*y ≤ H at hi
          dsimp only [b'] at hi
          rw [b.weight_extend,hlast] at hi
          apply (le_div_iff₀ hW).mpr
          nlinarith only [hi]
        have hred := hreduction s hs ⟨n,b,hroot,hlast⟩ (by omega) (H/b.weight lam eps)
          (div_nonneg hH hW.le) hfloor hchildren x hx
        have hh := mul_le_mul_of_nonneg_left hred hW.le
        have herr := herrorWeight n b hroot
        have hid : b.weight lam eps*(C*(H/b.weight lam eps)+error) =
            C*H+b.weight lam eps*error := by field_simp
        rw [hid] at hh
        calc
          b.weight lam eps*x ≤ C*H+E := by linarith
          _ ≤ (C+1)*H := by linarith
          _ = (C+1)^(D-n+1)*(L+E) := by dsimp only [H]; rw [pow_succ]; ring
  intro n b hr x hx
  exact haux (b.state n) n b hr rfl x hx

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PolicyEnergyInduction
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual energies satisfy the scalar branch induction hypotheses -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (BranchState BranchStep branchExponent)

theorem PolicyEnergy.recursion_step {m K L N₀ : ℕ} {ε T : ℝ} {Ψ : ℝ → ℝ}
    (w₀ : Sphere (m+3)) (Γ : PolicyContext m)
    (hrec : PolicyRecursionBounds m K L Γ.J Γ.lam Γ.σ ε T Γ.Z N₀ Ψ)
    (hN : N₀ ≤ Γ.N) (hσ : 0 < Γ.σ) (hZ : 1 ≤ Γ.Z)
    (hprofile : Γ.policy = profileExcess (d := m+3) Γ.profile Γ.N)
    (hcover : ∀ b, ∀ w : Sphere (m+3), ∃ c ∈ Γ.masks b,
      dist w c ≤ descriptorMaskRadius Γ.N Γ.σ b/2)
    (hq : Γ.σ*(Γ.N:ℝ) ≤ Γ.q)
    (hceil : ⌈10*Γ.σ*(Γ.N:ℝ)⌉₊ < Γ.q) (hq10 : 10*Γ.σ*(Γ.N:ℝ) ≤ Γ.q)
    (s : BranchState) (hs : s.Valid Γ.N Γ.σ) (hi : s.index+1 ≤ Γ.J)
    (hwide : s.start+100*Γ.q < s.finish) (M : ℝ) (hM : 0 ≤ M)
    (hfloor : ((2:ℝ)^Γ.N)^(4*(((m+3:ℕ):ℝ)+1)*Γ.lam+ε) ≤ M)
    (hchildren : ∀ u l, BranchStep Γ.policy Γ.N Γ.q Γ.σ s l u →
      ∀ x, PolicyEnergy K L Ψ w₀ Γ u x →
        ((2:ℝ)^Γ.N)^(branchExponent Γ.policy
          (dimensionalBranchReserve (m+3) Γ.lam Γ.σ) Γ.σ ε s l u)*x ≤ M)
    (x : ℝ) (hx : PolicyEnergy K L Ψ w₀ Γ s x) :
    x ≤ 3*M+((2:ℝ)^Γ.N)^(-T) := by
  cases hx with
  | positive P hleft hright hlo hhi =>
    exact P.positive_energy_step w₀ hrec hN hi hprofile hleft hright hwide hq
      (fun b _ => hcover b) hlo hhi M hM hfloor hchildren
  | angular P =>
    exact P.angular_energy_step w₀ hrec hN hi hσ hZ hprofile hs.2.2.2.2
      hwide hq hceil hq10 M hM hchildren

theorem eventual_policyEnergy_terminal (m K : ℕ) {ε W : ℝ}
    (hε : 0 < ε) (hW : 0 ≤ W) (Ψ : ℝ → ℝ)
    (hΨW : ∀ u, Ψ u ≤ W) (hsupp : ∀ u, 4 < u → Ψ u = 0) :
    ∃ N₀ : ℕ, ∀ (Γ : PolicyContext m) (L : ℕ), N₀ ≤ Γ.N → 1 ≤ Γ.Z →
      ∀ (w₀ : Sphere (m+3)) (s : BranchState), s.Valid Γ.N Γ.σ →
      s.finish ≤ s.start+100*Γ.q → ∀ x, PolicyEnergy K L Ψ w₀ Γ s x →
      x ≤ ((2:ℝ)^Γ.N)^(100*((m+3:ℕ):ℝ)*Γ.q/Γ.N+4*(((m+3:ℕ):ℝ)+1)*Γ.lam+ε) := by
  obtain ⟨N₀,hterm⟩ := eventual_policy_angular_terminal m K hε hW Ψ hΨW hsupp
  refine ⟨N₀,?_⟩
  intro Γ L hN hZ w₀ s hs hw x hx
  cases hx with
  | positive P hleft hright hlo hhi =>
    let := P.regular.probability
    have hp := positiveCollisionCount_terminal w₀ P.Q P.ρ P.regular P.N_pos P.policy
      P.σ P.J P.i P.q (hs.1.trans hs.2) hs.1 hw P.X P.Y P.X_length P.Y_length
    have hpr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hp
    rw [ENNReal.toReal_ofReal (by positivity)] at hpr
    apply hpr.trans
    apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
    change 100*(P.q:ℝ)/P.N+4*(((m+3:ℕ):ℝ)+1)*P.lam ≤
      100*((m+3:ℕ):ℝ)*P.q/P.N+4*(((m+3:ℕ):ℝ)+1)*P.lam+ε
    have hd : (1:ℝ) ≤ (m+3:ℕ) := by exact_mod_cast (show 1 ≤ m+3 by omega)
    have hm : (100:ℝ)*P.q/P.N ≤ 100*((m+3:ℕ):ℝ)*P.q/P.N := by
      calc
        _ = 100*1*(P.q:ℝ)/P.N := by ring
        _ ≤ _ := by gcongr
    linarith
  | angular P =>
    exact hterm P L hN ((hs.2.1.trans hs.2.2.1).trans hs.2.2.2.1) hw hZ

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PolicyWeightedRecursion
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted induction for the actual all-dimensional policy energies -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap ContDiff
open PlanarFalconer (BranchState PolicyBranch sourcePolicyBlock sourceSmoothingLevels)

theorem PolicyEnergy.profile_lipschitz {m K L : ℕ} {Ψ : ℝ → ℝ}
    {w₀ : Sphere (m+3)} {Γ : PolicyContext m} {s : BranchState} {x : ℝ}
    (hx : PolicyEnergy K L Ψ w₀ Γ s x)
    (hprofile : Γ.policy = profileExcess (d := m+3) Γ.profile Γ.N) :
    DimensionalProfileLipschitz (m+3) Γ.policy Γ.N := by
  cases hx with
  | positive P _ _ _ _ =>
    change DimensionalProfileLipschitz (m+3) P.policy P.N
    change P.policy = profileExcess (d := m+3) P.profile P.N at hprofile
    rw [hprofile]
    exact profileExcess_dimensional_lipschitz P.regular P.N_pos
  | angular P =>
    change DimensionalProfileLipschitz (m+3) P.policy P.N
    change P.policy = profileExcess (d := m+3) P.profile P.N at hprofile
    rw [hprofile]
    exact profileExcess_dimensional_lipschitz P.regular P.N_pos

theorem exists_policy_weighted_recursion
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {lam σ κ η T : ℝ} (hlam : 0 ≤ lam) (hσ : 0 < σ)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hgap : σ < κ/1000)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hloss : 4000*(dimensionalBranchReserve (m+3) lam σ+σ) ≤ 1)
    (hT : (20/κ+1/σ)*(3*((m+3:ℕ):ℝ)+2)+10 < T)
    (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ) (hφ : ∀ r, φ r = (Ψ r : ℂ))
    (hΨ : Measurable Ψ) (hsmooth : ContDiff ℝ ∞ Ψ)
    (hpos : ∀ r, 0 ≤ Ψ r) (hzero : ∀ r ≤ 0, Ψ r = 0)
    (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
    {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) (minJet : ℕ := 0) :
    ∃ (K L : ℕ) (Z : ℝ) (N₀ : ℕ), minJet ≤ K ∧ 1 ≤ Z ∧ 0 < N₀ ∧
      ∀ (Γ : PolicyContext m), Γ.lam = lam → Γ.σ = σ →
      Γ.J = sourceSmoothingLevels σ κ → Γ.q = sourcePolicyBlock Γ.N κ → Γ.Z = Z →
      N₀ ≤ Γ.N → Γ.policy = profileExcess (d := m+3) Γ.profile Γ.N →
      (∀ b, ∀ w : Sphere (m+3), ∃ c ∈ Γ.masks b,
        dist w c ≤ descriptorMaskRadius Γ.N Γ.σ b/2) →
      ∀ (w₀ : Sphere (m+3)) (root : BranchState), root.Valid Γ.N σ → root.index = 0 →
      root.start+100*sourcePolicyBlock Γ.N κ < root.finish →
      ∀ x, PolicyEnergy K L Ψ w₀ Γ root x →
      x ≤ 4^(sourceSmoothingLevels σ κ+1)*
        (((2:ℝ)^Γ.N)^(2*Γ.policy root.start-
          PlanarFalconer.potential Γ.policy root.start root.finish (10*sourcePolicyBlock Γ.N κ)+
          500*((m+3:ℕ):ℝ)*κ+10^6*(dimensionalBranchReserve (m+3) lam σ+σ)/κ+η)+
          ((2:ℝ)^Γ.N)^(-10:ℝ)) := by
  let ε := η/(2*(1+20/κ+1/σ))
  let reserve := dimensionalBranchReserve (m+3) lam σ
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεη : ε ≤ η/2 := by
    dsimp [ε]
    apply (div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)).mpr
    have hh : 0 ≤ 20/κ+1/σ := by positivity
    nlinarith
  have hε1 : ε ≤ 1 := by linarith
  have hreserve : 0 ≤ reserve := dimensionalBranchReserve_nonneg (m+3) hlam hσ.le
  have hσ1 : σ ≤ 1 := by linarith
  have hTp : 0 ≤ T := by
    have hh : 0 < (20/κ+1/σ)*(3*((m+3:ℕ):ℝ)+2) := by positivity
    linarith
  have hJ : 0 < sourceSmoothingLevels σ κ := by
    have hh := PlanarFalconer.source_smoothing_reserve hσ hκ
    have hh' : 0 < 1+20/κ+1/σ := by positivity
    exact_mod_cast (lt_trans hh' hh)
  obtain ⟨K,L,Z,Nr,hminJet,hZ,hrec⟩ := exists_policy_recursion_bounds hgnomonic hquadratic m
    hlam hσ hσ1 hε hTp hJ φ Ψ hφ hΨ hsmooth hpos hzero hone hV hΨV hsupp minJet
  obtain ⟨Nt,hterm⟩ := eventual_policyEnergy_terminal m K (half_pos hη) hV Ψ hΨV
    (fun u hu => by by_contra hn; exact (not_lt_of_ge (hsupp u hn).2.le) hu)
  obtain ⟨Nw,_,hweight⟩ := dimensional_uniform_source_weighted_terminal
    (d := m+3) hreserve hσ hκ hκ1 hgap hη
  obtain ⟨Ne,_,herror⟩ := dimensional_uniform_source_weighted_error
    (d := m+3) hσ hκ hκ1 hgap hloss hε1 hT
  obtain ⟨Nv,_,hvalid⟩ := PlanarFalconer.uniform_branch_successor_validity hσ hκ hgap
  obtain ⟨Nd,_,hdepth⟩ := PlanarFalconer.uniform_source_branch_depth hσ hκ hκ1 hgap
  obtain ⟨Ns,_,hslack⟩ := PlanarFalconer.uniform_source_ceiling_slack hσ hgap
  let N₀ := Nr+Nt+Nw+Ne+Nv+Nd+Ns+1
  refine ⟨K,L,Z,N₀,hminJet,hZ,by dsimp [N₀]; omega,?_⟩
  intro Γ hLam hσΓ hJG hqΓ hZΓ hN hprofile hcover w₀ root hroot hindex hwide x hx
  have hNr : Nr ≤ Γ.N := by dsimp [N₀] at hN; omega
  have hNt : Nt ≤ Γ.N := by dsimp [N₀] at hN; omega
  have hNw : Nw ≤ Γ.N := by dsimp [N₀] at hN; omega
  have hNe : Ne ≤ Γ.N := by dsimp [N₀] at hN; omega
  have hNv : Nv ≤ Γ.N := by dsimp [N₀] at hN; omega
  have hNd : Nd ≤ Γ.N := by dsimp [N₀] at hN; omega
  have hNs : Ns ≤ Γ.N := by dsimp [N₀] at hN; omega
  have hNp : 0 < Γ.N := by dsimp [N₀] at hN; omega
  have hA := hx.profile_lipschitz hprofile
  let R : ℝ := (2:ℝ)^Γ.N
  let terminal : ℝ := R^(200*((m+3:ℕ):ℝ)*(sourcePolicyBlock Γ.N κ:ℝ)/Γ.N+12*reserve+η/2)
  let floor : ℝ := R^(4*(((m+3:ℕ):ℝ)+1)*lam+ε)
  let B : ℝ := R^(2*Γ.policy root.start-
    PlanarFalconer.potential Γ.policy root.start root.finish (10*sourcePolicyBlock Γ.N κ)+
    500*((m+3:ℕ):ℝ)*κ+10^6*(reserve+σ)/κ+η)
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hpaid : 4*(((m+3:ℕ):ℝ)+1)*lam ≤ 12*reserve := by
    dsimp [reserve,dimensionalBranchReserve]
    nlinarith [mul_nonneg (show 0 ≤ ((m+3:ℕ):ℝ)+1 by positivity) hlam,
      mul_nonneg (show 0 ≤ ((m+3:ℕ):ℝ)+1 by positivity) hσ.le]
  have hfloorTerminal : floor ≤ terminal := by
    apply Real.rpow_le_rpow_of_exponent_le hR
    have hh : 0 ≤ 200*((m+3:ℕ):ℝ)*(sourcePolicyBlock Γ.N κ:ℝ)/Γ.N := by positivity
    linarith
  have hrecΓ : PolicyRecursionBounds m K L Γ.J Γ.lam Γ.σ ε T Γ.Z Nr Ψ := by
    simpa only [hLam,hσΓ,hJG,hZΓ] using hrec
  have hind := PlanarFalconer.weighted_branch_energy_induction Γ.policy Γ.N
    (sourcePolicyBlock Γ.N κ) (sourceSmoothingLevels σ κ) σ reserve ε 3 terminal floor
    (R^(-T)) B (R^(-10:ℝ)) root (PolicyEnergy K L Ψ w₀ Γ)
    hNp (PlanarFalconer.sourcePolicyBlock_pos hNp hκ) hσ (by norm_num)
    (by dsimp [B]; positivity) (by positivity)
    (fun s u l hs hstep => (hvalid Γ.N hNv Γ.policy s u l hs hstep).1)
    (by
      intro n b hb
      have hi : (b.state 0).index = 0 := by rw [hb]; exact hindex
      have hn := (hdepth Γ.N hNd Γ.policy n b hi).2.2.1
      have hh := PlanarFalconer.source_smoothing_reserve hσ hκ
      have hn' : (n:ℝ) < sourceSmoothingLevels σ κ := by linarith
      exact (Nat.cast_lt.mp hn').le)
    (by
      intro s hs hstop y hy
      have hsΓ : s.Valid Γ.N Γ.σ := by simpa only [hσΓ] using hs
      have hstopΓ : s.finish ≤ s.start+100*Γ.q := by simpa only [hqΓ] using hstop
      have ht := hterm Γ L hNt (by simpa only [hZΓ] using hZ) w₀ s hsΓ hstopΓ y hy
      apply ht.trans
      apply Real.rpow_le_rpow_of_exponent_le hR
      rw [hLam,hqΓ]
      change 100*((m+3:ℕ):ℝ)*(sourcePolicyBlock Γ.N κ:ℝ)/Γ.N+
        4*(((m+3:ℕ):ℝ)+1)*lam+η/2 ≤ _
      have hw : 100*((m+3:ℕ):ℝ)*(sourcePolicyBlock Γ.N κ:ℝ)/Γ.N ≤
          200*((m+3:ℕ):ℝ)*(sourcePolicyBlock Γ.N κ:ℝ)/Γ.N := by
        gcongr
        norm_num
      exact add_le_add_left (add_le_add hw hpaid) (η/2))
    (by
      intro s hs hreached hw M hM hfloor hchildren y hy
      obtain ⟨n,b,hb,hsb⟩ := hreached
      have hi : (b.state 0).index = 0 := by rw [hb]; exact hindex
      have hsi := ((hdepth Γ.N hNd Γ.policy n b hi).2.2.2 n le_rfl).2
      rw [hsb] at hsi
      apply PolicyEnergy.recursion_step w₀ Γ hrecΓ hNr
        (by simpa only [hσΓ] using hσ) (by simpa only [hZΓ] using hZ) hprofile hcover
        (by simpa only [hσΓ,hqΓ] using (hslack Γ.N hNs).2.2)
        (by simpa only [hσΓ,hqΓ] using (hslack Γ.N hNs).1)
        (by simpa only [hσΓ,hqΓ] using (hslack Γ.N hNs).2.1)
        s (by simpa only [hσΓ] using hs) (by simpa only [hJG] using hsi.le)
        (by simpa only [hqΓ] using hw) M hM
        (by simpa only [floor,R,hLam] using hfloor) ?_ y hy
      intro u l hstep z hz
      have hstep' : PlanarFalconer.BranchStep Γ.policy Γ.N (sourcePolicyBlock Γ.N κ) σ s l u := by
        simpa only [hσΓ,hqΓ] using hstep
      simpa only [hσΓ,hLam,reserve,R] using hchildren u l hstep' z hz)
    (by
      intro n b hb
      have hw := hweight Γ.N hNw Γ.policy hA n b (by rw [hb]; omega)
      simpa only [hb,ε,terminal,B,R] using hw)
    (by
      intro n b hb
      apply (mul_le_mul_of_nonneg_left hfloorTerminal (b.weight_pos reserve ε).le).trans
      have hw := hweight Γ.N hNw Γ.policy hA n b (by rw [hb]; omega)
      simpa only [hb,ε,terminal,B,R] using hw)
    (by
      intro n b hb
      apply herror Γ.N hNe Γ.policy hA n b
      rw [hb]
      exact hindex)
  let b₀ : PolicyBranch Γ.policy Γ.N (sourcePolicyBlock Γ.N κ) σ 0 :=
    ⟨fun _ => root,fun _ => .low,fun _ _ => hroot,by omega⟩
  have hb := hind 0 b₀ rfl x hx
  simpa only [PolicyBranch.weight_zero,one_mul,Nat.sub_zero,B,R,reserve,
    show (3:ℝ)+1 = 4 by norm_num] using hb

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PolicyRootApplication
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The weighted estimate on actual positive and angular root states -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap ContDiff
open PlanarFalconer (sourcePolicyBlock sourceSmoothingLevels)

theorem exists_policy_root_bounds
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {lam σ κ η T : ℝ} (hlam : 0 ≤ lam) (hσ : 0 < σ)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hgap : σ < κ/1000)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hloss : 4000*(dimensionalBranchReserve (m+3) lam σ+σ) ≤ 1)
    (hT : (20/κ+1/σ)*(3*((m+3:ℕ):ℝ)+2)+10 < T)
    (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ) (hφ : ∀ r, φ r = (Ψ r : ℂ))
    (hΨ : Measurable Ψ) (hsmooth : ContDiff ℝ ∞ Ψ)
    (hpos : ∀ r, 0 ≤ Ψ r) (hzero : ∀ r ≤ 0, Ψ r = 0)
    (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
    {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) (minJet : ℕ := 0) :
    ∃ (K L : ℕ) (Z : ℝ) (N₀ : ℕ), minJet ≤ K ∧ 1 ≤ Z ∧ 0 < N₀ ∧
      ∀ P : PolicyJetData m, P.lam = lam → P.σ = σ →
      P.J = sourceSmoothingLevels σ κ → P.q = sourcePolicyBlock P.N κ → P.Z = Z →
      N₀ ≤ P.N → P.i = 0 → P.policy = profileExcess (d := m+3) P.profile P.N →
      (∀ b, ∀ w : Sphere (m+3), ∃ c ∈ P.masks b,
        dist w c ≤ descriptorMaskRadius P.N P.σ b/2) →
      P.a+100*P.q < P.t → ∀ w₀ : Sphere (m+3),
      (P.a₀ = P.a → P.t₀ = P.t →
        125*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side ≤
          ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ →
        ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ ≤
          2000*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side →
        P.positiveCount w₀ ≤ P.rootBound σ κ η) ∧
      ((P.t₀:ℝ) ≤ P.t+P.σ*P.N → P.envelope K L Ψ ≤ P.rootBound σ κ η) := by
  obtain ⟨K,L,Z,N₀,hminJet,hZ,hN₀,hbound⟩ := exists_policy_weighted_recursion
    hgnomonic hquadratic m hlam hσ hκ hκ1 hgap hη hη1 hloss hT
    φ Ψ hφ hΨ hsmooth hpos hzero hone hV hΨV hsupp minJet
  refine ⟨K,L,Z,N₀,hminJet,hZ,hN₀,?_⟩
  intro P hLam hσP hJ hq hZP hN hi hprofile hcover hwide w₀
  have hwide' : P.a+100*sourcePolicyBlock P.N κ < P.t := by simpa only [hq] using hwide
  constructor
  · intro hleft hright hlo hhi
    have hs := P.positiveBranchState_valid (by omega : P.a ≤ P.t)
    have hb := hbound P.context hLam hσP hJ hq hZP hN hprofile hcover w₀
      P.positiveBranchState (by simpa only [PolicyJetData.context,hσP] using hs) hi hwide'
      (P.positiveCount w₀) (.positive P hleft hright hlo hhi)
    simpa only [PolicyJetData.rootBound,PolicyJetData.context,
      PolicyJetData.positiveBranchState,PlanarFalconer.BranchState.start,
      PlanarFalconer.BranchState.finish,hLam] using hb
  · intro hbase
    have hs := P.branchState_valid (by omega : P.a ≤ P.t) hbase
    have hb := hbound P.context hLam hσP hJ hq hZP hN hprofile hcover w₀
      P.branchState (by simpa only [PolicyJetData.context,hσP] using hs) hi hwide'
      (P.envelope K L Ψ) (.angular P)
    simpa only [PolicyJetData.rootBound,PolicyJetData.context,
      PolicyJetData.branchState,PlanarFalconer.BranchState.start,
      PlanarFalconer.BranchState.finish,hLam] using hb

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_NormalizedSpatialFactors
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact restoration of normalized factors under the original endpoint integrals

The positive endpoint sizes are constants in every spatial, spherical and
radial variable. Pulling them through the integrals preserves the original
measures and gives their exact squared cost in the shell estimate.
-/

namespace Falconer
open Set MeasureTheory
open scoped ComplexConjugate

variable {d : ℕ}

theorem endpointTransform_const_mul (μ : Measure (Space d)) (M : ℝ)
    (b : Space d → Sphere d → ℂ) (c : ℂ) (r : ℝ) (w : Sphere d) :
    endpointTransform μ M (fun x w => c*b x w) r w =
      c*endpointTransform μ M b r w := by
  unfold endpointTransform
  have he : (fun x => Complex.exp (Complex.I*(r : ℂ)*(inner ℝ (w : Space d) x : ℂ))*
      (c*b x w)) = fun x => c*(Complex.exp
        (Complex.I*(r : ℂ)*(inner ℝ (w : Space d) x : ℂ))*b x w) := by
    funext x
    ring
  rw [he,integral_const_mul,mul_smul_comm]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetNormalization
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Changing the fixed normalization of the exact jet envelope -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

namespace DescriptorJetSymbol

theorem value_renormalize {n K L : ℕ} {F : Finset PolicyDescriptor} {D : ℝ}
    (f : DescriptorJetSymbol n K L F D)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    {A B : ℝ} (hB : B ≠ 0) :
    f.value Q ρ m N σ J i S A =
      fun x w => ((B/A : ℝ) : ℂ)*f.value Q ρ m N σ J i S B x w := by
  funext x w
  unfold value multiplier
  simp only [Complex.ofReal_div,Complex.ofReal_inv]
  have hBc : (B : ℂ) ≠ 0 := by exact_mod_cast hB
  field_simp

end DescriptorJetSymbol

theorem jetStateEnvelope_renormalize {n K L : ℕ} {D : ℝ} {F G : Finset PolicyDescriptor}
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (μ ν : Measure (Space (n+2))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)] :
    jetStateEnvelope n K L D F G Q ρ m N σ J i S A μ ν M P a v Ψ ≤
      (B/A)^4*jetStateEnvelope n K L D F G Q ρ m N σ J i S B μ ν M P a v Ψ := by
  have hratio : 0 ≤ B/A := div_nonneg hB.le hA.le
  have hbound : 0 ≤ (descriptorJetBound (n+2) K)^K*B⁻¹ := by
    have := descriptorJetBound_one_le (n+2) K
    positivity
  have henv : 0 ≤ jetStateEnvelope n K L D F G Q ρ m N σ J i S B μ ν M P a v Ψ :=
    le_csSup (jetStateValues_bddAbove Q ρ m N σ J i S hF hG hB μ ν hM hP a v Ψ) (Or.inl rfl)
  apply csSup_le (show (jetStateValues n K L D F G Q ρ m N σ J i S A μ ν M P a v Ψ).Nonempty
    from ⟨0,Or.inl rfl⟩)
  intro x hx
  rcases hx with rfl | ⟨f,g,rfl⟩
  · exact mul_nonneg (pow_nonneg hratio _) henv
  · have hf := f.value_renormalize Q ρ m N σ J i S (A := A) hB.ne'
    have hg := g.value_renormalize Q ρ m N σ J i S (A := A) hB.ne'
    have h := independentAngularEnergy_endpoint_remove_factors μ ν hM hP
      (f.value Q ρ m N σ J i S B) (g.value Q ρ m N σ J i S B)
      (f.value_measurable Q ρ m N σ J i S B) (g.value_measurable Q ρ m N σ J i S B)
      hbound hbound (f.value_norm_le Q ρ m N σ J i S hF hB)
      (g.value_norm_le Q ρ m N σ J i S hG hB)
      (fun _ => ((B/A : ℝ) : ℂ)) (fun _ => ((B/A : ℝ) : ℂ))
      measurable_const measurable_const hratio hratio
      (fun _ => by simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hratio,le_refl])
      (fun _ => by simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hratio,le_refl]) a v Ψ
    have hpow : (B/A)^2*(B/A)^2 = (B/A)^4 := by ring
    rw [hpow] at h
    have he : jetStateEnergy Q ρ m N σ J i S A μ ν M P a v Ψ f g ≤
        (B/A)^4*jetStateEnergy Q ρ m N σ J i S B μ ν M P a v Ψ f g := by
      unfold jetStateEnergy
      rw [hf,hg]
      simpa only [endpointTransform_const_mul] using h
    exact he.trans (mul_le_mul_of_nonneg_left
      (jetStateEnergy_le_envelope Q ρ m N σ J i S hF hG hB μ ν hM hP a v Ψ f g)
      (pow_nonneg hratio _))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_FlexibleAngularRoot
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Applying the recursive root estimate at the outer graph budgets -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap ContDiff
open PlanarFalconer (sourcePolicyBlock sourceSmoothingLevels)

theorem exists_flexible_angular_root
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {lam σ κ η T : ℝ} (hlam : 0 ≤ lam) (hσ : 0 < σ)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hgap : σ < κ/1000)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hloss : 4000*(dimensionalBranchReserve (m+3) lam σ+σ) ≤ 1)
    (hT : (20/κ+1/σ)*(3*((m+3:ℕ):ℝ)+2)+10 < T)
    (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ) (hφ : ∀ r, φ r = (Ψ r : ℂ))
    (hΨ : Measurable Ψ) (hsmooth : ContDiff ℝ ∞ Ψ)
    (hpos : ∀ r, 0 ≤ Ψ r) (hzero : ∀ r ≤ 0, Ψ r = 0)
    (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
    {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) (minJet : ℕ) :
    ∃ (K L : ℕ) (Z : ℝ) (N₀ : ℕ), minJet ≤ K ∧ 1 ≤ Z ∧ 0 < N₀ ∧
      ∀ k l : ℕ, k ≤ K → L ≤ l →
      ∀ P : PolicyJetData m, P.lam = lam → P.σ = σ →
      P.J = sourceSmoothingLevels σ κ → P.q = sourcePolicyBlock P.N κ →
      N₀ ≤ P.N → P.i = 0 → P.policy = profileExcess (d := m+3) P.profile P.N →
      (∀ b, ∀ w : Sphere (m+3), ∃ c ∈ P.masks b,
        dist w c ≤ descriptorMaskRadius P.N P.σ b/2) →
      P.a+100*P.q < P.t → (P.t₀:ℝ) ≤ P.t+P.σ*P.N →
      P.envelope k l Ψ ≤ (Z/P.Z)^4*P.rootBound σ κ η := by
  obtain ⟨K,L,Z,N₀,hK,hZ,hN₀,hroot⟩ := exists_policy_root_bounds
    hgnomonic hquadratic m hlam hσ hκ hκ1 hgap hη hη1 hloss hT
    φ Ψ hφ hΨ hsmooth hpos hzero hone hV hΨV hsupp minJet
  refine ⟨K,L,Z,N₀,hK,hZ,hN₀,?_⟩
  intro k l hk hl P hLam hσP hJ hq hN hi hprofile hcover hwide hbase
  let P' := P.withNormalization Z (zero_lt_one.trans_le hZ)
  have hroot' : P'.envelope K L Ψ ≤ P.rootBound σ κ η :=
    (hroot P' hLam hσP hJ hq rfl hN hi hprofile hcover hwide
      (gnomonicChart (0 : Space (m+2)))).2 hbase
  let := P.regular.probability
  let := P'.regular.probability
  let := PlanarFalconer.sourceAngularShellMeasure_finite (P.t:ℝ) Ψ hV hΨV
    (fun u hu => by by_contra hn; exact (not_lt_of_ge hu.le) (hsupp u hn).2)
  have hmass : 0 < profileModelMass P.profile P.N P.a := by unfold profileModelMass; positivity
  have hnorm : P.envelope k l Ψ ≤ (Z/P.Z)^4*P'.envelope k l Ψ :=
    jetStateEnvelope_renormalize P.Q P.ρ (fun u => P.profile (u/P.N))
      P.N P.σ P.J P.i P.masks P.separated P.separated P.Z_pos P'.Z_pos
      _ _ hmass hmass P.a P.t Ψ
  have hbudget : P'.envelope k l Ψ ≤ P'.envelope K L Ψ :=
    jetStateEnvelope_budget_mono hk hl (by norm_num) le_rfl
      P.Q P.ρ (fun u => P.profile (u/P.N)) P.N P.σ P.J P.i P.masks
      P.separated P.separated P'.Z_pos _ _ hmass hmass P.a P.t Ψ
  exact hnorm.trans (mul_le_mul_of_nonneg_left (hbudget.trans hroot') (by positivity))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_FlexibleGraphChild
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Applying the recursive estimate to the actual outer graph children -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap ContDiff
open PlanarFalconer (sourcePolicyBlock sourceSmoothingLevels)

theorem exists_flexible_graph_child_oai
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {lam σ κ η T : ℝ} (hlam : 0 ≤ lam) (hσ : 0 < σ)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hgap : σ < κ/1000)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hloss : 4000*(dimensionalBranchReserve (m+3) lam σ+σ) ≤ 1)
    (hT : (20/κ+1/σ)*(3*((m+3:ℕ):ℝ)+2)+10 < T)
    (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ) (hφ : ∀ r, φ r = (Ψ r : ℂ))
    (hΨ : Measurable Ψ) (hsmooth : ContDiff ℝ ∞ Ψ)
    (hpos : ∀ r, 0 ≤ Ψ r) (hzero : ∀ r ≤ 0, Ψ r = 0)
    (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
    {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) (minJet : ℕ) :
    ∃ (K L : ℕ) (Z : ℝ) (N₀ : ℕ), minJet ≤ K ∧ 1 ≤ Z ∧ 0 < N₀ ∧
      ∀ k l : ℕ, k ≤ K → L ≤ l →
      ∀ P : PolicyJetData m, P.lam = lam → P.σ = σ →
      P.J = sourceSmoothingLevels σ κ → P.q = sourcePolicyBlock P.N κ →
      N₀ ≤ P.N → P.i = 0 → P.policy = profileExcess (d := m+3) P.profile P.N →
      (∀ b, ∀ w : Sphere (m+3), ∃ c ∈ P.masks b,
        dist w c ≤ descriptorMaskRadius P.N P.σ b/2) →
      (P.t₀:ℝ) ≤ P.t+P.σ*P.N →
      ∀ c : ℕ, P.a ≤ c → c+100*P.q < P.t →
      P.graphChild k l c Ψ ≤ (Z/P.Z)^4*P.rootBoundAt c σ κ η := by
  obtain ⟨K,L,Z,N₀,hK,hZ,hN₀,hroot⟩ := exists_flexible_angular_root
    hgnomonic hquadratic m hlam hσ hκ hκ1 hgap hη hη1 hloss hT
    φ Ψ hφ hΨ hsmooth hpos hzero hone hV hΨV hsupp minJet
  refine ⟨K,L,Z,N₀,hK,hZ,hN₀,?_⟩
  intro k l hk hl P hLam hσP hJ hq hN hi hprofile hcover hbase c hac hwide
  apply P.graphChild_le k l c hac Ψ (by unfold PolicyJetData.rootBoundAt; positivity)
  intro row hrow
  have hb := hroot k l hk hl (P.child c hac row hrow)
    hLam hσP hJ hq hN hi hprofile hcover hwide hbase
  exact hb

end Falconer

end OAI
end

theorem solution : type_of% @OAI.Falconer.exists_flexible_graph_child_oai := @OAI.Falconer.exists_flexible_graph_child_oai
