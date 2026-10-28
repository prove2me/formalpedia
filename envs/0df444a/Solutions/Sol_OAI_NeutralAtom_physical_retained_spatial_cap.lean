-- Prove2me | solution 1 for OAI.NeutralAtom.physical_retained_spatial_cap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:37:07.735247+00:00
-- url     : https://prove2.me/submissions/cf0c5185-d61c-4671-9ad9-45fa3b1fd7e6

import Mathlib
import Definitions.Def_CoulombRadii
import Definitions.Def_OAIQ062C008

section
-- module Solutions.OAIQ062_CR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_NewtonSubmean
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
namespace Coulomb

lemma ballCloud_coulomb_le {a M : ℝ} (ha : 0<a) (hM : 0≤M) (y x : Space) (hxy : x≠y) :
    (∫ z, coulombKernel (x-z)*ballCloud y a M z) ≤ M*coulombKernel (x-y) := by
  have he : (∫ z, coulombKernel (x-z)*ballCloud y a M z) =
      ∫ z, coulombKernel ((x-y)-z)*uniformBall a M z := by
    rw [← integral_sub_right_eq_self (fun z => coulombKernel ((x-y)-z)*uniformBall a M z) y]
    apply integral_congr_ae
    filter_upwards [] with z
    change coulombKernel (x-z)*uniformBall a M (z-y) = _
    rw [show (x-y)-(z-y)=x-z by abel]
  rw [he]
  have H := radial_coulomb_integral_le (uniformBall_integrable a M) (uniformBall_measurable a M)
    (uniformBall_nonneg ha hM) (uniformBall_le ha hM) (uniformBall_radial a M) (sub_ne_zero.mpr hxy)
  simpa only [uniformBall_mass ha,mul_comm M] using H

lemma potentialOf_ballCloud_integrable {ρ : Space → ℝ} (hi : Integrable ρ) (hm : Measurable ρ)
    {a : ℝ} (ha : 0<a) (y : Space) :
    Integrable (fun z => NeutralAtom.potentialOf ρ z*ballCloud y a 1 z) := by
  have H := (coulomb_pair_integrable hi hm (ballCloud_integrable a 1 y) (ballCloud_measurable a 1 y)
    (fun z => by
      change ‖uniformBall a 1 (z-y)‖ ≤ _
      rw [Real.norm_eq_abs,abs_of_nonneg (uniformBall_nonneg ha zero_le_one (z-y))]
      exact uniformBall_le ha zero_le_one (z-y))).integral_prod_right
  apply H.congr
  filter_upwards [] with z
  simp only [NeutralAtom.potentialOf,←integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with x
  change ρ x*ballCloud y a 1 z*coulombKernel (x-z) = coulombKernel (z-x)*ρ x*ballCloud y a 1 z
  rw [coulombKernel_sub_comm x z]
  ring

lemma potentialOf_ballCloud_le {ρ : Space → ℝ} (hi : Integrable ρ) (hm : Measurable ρ)
    (hp : ∀ x, 0≤ρ x) {a : ℝ} (ha : 0<a) (y : Space)
    (hK : Integrable (fun x => coulombKernel (y-x)*ρ x)) :
    (∫ z, NeutralAtom.potentialOf ρ z*ballCloud y a 1 z) ≤ NeutralAtom.potentialOf ρ y := by
  have H := coulomb_pair_integrable hi hm (ballCloud_integrable a 1 y) (ballCloud_measurable a 1 y)
    (fun z => by
      change ‖uniformBall a 1 (z-y)‖ ≤ _
      rw [Real.norm_eq_abs,abs_of_nonneg (uniformBall_nonneg ha zero_le_one (z-y))]
      exact uniformBall_le ha zero_le_one (z-y))
  have he : (∫ z, NeutralAtom.potentialOf ρ z*ballCloud y a 1 z) =
      ∫ x, ∫ z, ρ x*ballCloud y a 1 z*coulombKernel (x-z) := by
    rw [integral_integral_swap H]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [NeutralAtom.potentialOf,←integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with x
    change coulombKernel (z-x)*ρ x*ballCloud y a 1 z = ρ x*ballCloud y a 1 z*coulombKernel (x-z)
    rw [coulombKernel_sub_comm z x]
    ring
  rw [he]
  apply integral_mono_ae H.integral_prod_left hK
  filter_upwards [volume.ae_ne y] with x hxy
  have hh := mul_le_mul_of_nonneg_left (ballCloud_coulomb_le ha zero_le_one y x hxy) (hp x)
  simpa only [←integral_const_mul,one_mul,coulombKernel_sub_comm y x,mul_left_comm,mul_comm,mul_assoc] using hh

end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
namespace Coulomb

lemma closedBall_ae_ball (y : Space) (a : ℝ) :
    Metric.closedBall y a =ᵐ[volume] Metric.ball y a := by
  filter_upwards [(measure_eq_zero_iff_ae_notMem).mp (Measure.addHaar_sphere volume y a)] with x hx
  apply propext
  simp only [Metric.mem_closedBall,Metric.mem_ball,Metric.mem_sphere] at *
  exact ⟨fun h => lt_of_le_of_ne h hx,le_of_lt⟩

lemma integral_ballCloud (F : Space → ℝ) (y : Space) (a : ℝ) :
    (∫ x, F x*ballCloud y a 1 x) =
      (4*Real.pi/3*a^3)⁻¹*(∫ x in Metric.closedBall y a, F x) := by
  have he : (fun x => F x*ballCloud y a 1 x) =
      (Metric.ball y a).indicator (fun x => F x*(4*Real.pi/3*a^3)⁻¹) := by
    funext x
    have hd : x-y∈Metric.ball (0:Space) a ↔ x∈Metric.ball y a := by
      simp only [Metric.mem_ball,dist_eq_norm,sub_zero]
    by_cases hx : x∈Metric.ball y a
    · simp only [ballCloud,uniformBall,indicator_of_mem hx,indicator_of_mem (hd.mpr hx),one_div]
    · simp only [ballCloud,uniformBall,indicator_of_notMem hx,indicator_of_notMem (not_congr hd |>.mpr hx),mul_zero]
  rw [he,integral_indicator measurableSet_ball,integral_mul_const,
    ←setIntegral_congr_set (closedBall_ae_ball y a),mul_comm]

lemma volume_closedBall_three (y : Space) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (Metric.closedBall y r) = 4*Real.pi/3*r^3 := by
  rw [Measure.addHaar_real_closedBall_eq_addHaar_real_ball,
    Measure.addHaar_real_ball_center,volume_real_ball_three r hr]

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_SmoothMultiplier
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

theorem memLp_bounded_real_smul {n : ℕ} {f : Configuration n → ℂ}
    (hf : MemLp f 2 volume) {θ : Configuration n → ℝ} (hθ : Continuous θ)
    (hb : ∃ C : ℝ, ∀ x, |θ x| ≤ C) : MemLp (fun x => θ x • f x) 2 volume := by
  obtain ⟨C,hC⟩ := hb
  apply hf.of_le_mul (c := C) (hθ.aestronglyMeasurable.smul hf.aestronglyMeasurable)
  exact Eventually.of_forall fun x => by
    change ‖θ x • f x‖ ≤ C * ‖f x‖
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

theorem integrable_test_real_smul {n : ℕ} {f : Configuration n → ℂ}
    (hf : MemLp f 2 volume) {φ : Configuration n → ℝ} (hφ : Continuous φ)
    (hc : HasCompactSupport φ) : Integrable (fun x => φ x • f x) := by
  exact (hf.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport hφ hc

theorem IsAntisymmetric.multiply {n : ℕ} {ψ : Wavefunction n}
    (hψ : IsAntisymmetric ψ) {θ : Configuration n → ℝ}
    (hθ : ∀ (p : Equiv.Perm (Fin n)) x, θ (x ∘ p) = θ x) :
    IsAntisymmetric (multiplyWavefunction θ ψ) := by
  intro p σ
  filter_upwards [hψ p σ] with x hx
  simp only [multiplyWavefunction, hθ p x, hx, mul_smul_comm]

theorem HasWeakGradient.multiply {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hg : HasWeakGradient ψ g) (hψ : ∀ σ, MemLp (ψ σ) 2 volume)
    (hgLp : ∀ σ i a, MemLp (g σ i a) 2 volume)
    {θ : Configuration n → ℝ} (hθ : ContDiff ℝ ∞ θ) :
    HasWeakGradient (multiplyWavefunction θ ψ) (multiplyGradient θ ψ g) := by
  intro σ i a φ hφ hφc
  let dθ : Configuration n → ℝ := fun x => fderiv ℝ θ x (coordinateDirection i a)
  let dφ : Configuration n → ℝ := fun x => fderiv ℝ φ x (coordinateDirection i a)
  have hdθ : Continuous dθ := (hθ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφ : Continuous dφ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφc : HasCompactSupport dφ := hφc.fderiv_apply ℝ _
  have hi₁ : Integrable (fun x => (θ x*dφ x) • ψ σ x) :=
    integrable_test_real_smul (hψ σ) (hθ.continuous.mul hdφ) hdφc.mul_left
  have hi₂ : Integrable (fun x => (φ x*dθ x) • ψ σ x) :=
    integrable_test_real_smul (hψ σ) (hφ.continuous.mul hdθ) hφc.mul_right
  have hi₃ : Integrable (fun x => (φ x*θ x) • g σ i a x) :=
    integrable_test_real_smul (hgLp σ i a)
    (hφ.continuous.mul hθ.continuous) hφc.mul_right
  have h := hg σ i a (fun x => φ x * θ x) (hφ.mul hθ) hφc.mul_right
  have hder : ∀ x, fderiv ℝ (fun x => φ x * θ x) x (coordinateDirection i a) =
      θ x*dφ x + φ x*dθ x := by
    intro x
    change (fderiv ℝ (φ * θ) x) _ = _
    rw [fderiv_mul (hφ.differentiable (by simp)).differentiableAt
      (hθ.differentiable (by simp)).differentiableAt]
    simp [dθ, dφ, smul_eq_mul, add_comm]
  simp_rw [hder] at h
  change (∫ x, (θ x*dφ x + φ x*dθ x) • ψ σ x) =
    -(∫ x, (φ x*θ x) • g σ i a x) at h
  simp_rw [add_smul] at h
  rw [integral_add hi₁ hi₂] at h
  change (∫ x, dφ x • (θ x • ψ σ x)) =
    -(∫ x, φ x • (dθ x • ψ σ x + θ x • g σ i a x))
  simp_rw [smul_add, smul_smul]
  rw [integral_add hi₂ hi₃]
  simp_rw [mul_comm (dφ _) (θ _)]
  linear_combination h

theorem norm_multiplyWavefunction_sq {n : ℕ} (θ : Configuration n → ℝ)
    (ψ : Wavefunction n) (σ : Spins n) (x : Configuration n) :
    ‖multiplyWavefunction θ ψ σ x‖^2 = θ x^2 * ‖ψ σ x‖^2 := by
  simp [multiplyWavefunction, mul_pow]

theorem integrable_weight_multiply {n : ℕ} {θ : Configuration n → ℝ}
    (hθ : Continuous θ) (hb : ∃ C : ℝ, ∀ x, |θ x| ≤ C)
    (ψ : Wavefunction n) (σ : Spins n) {W : Configuration n → ℝ}
    (hi : Integrable (fun x => W x*‖ψ σ x‖^2)) :
    Integrable (fun x => W x*‖multiplyWavefunction θ ψ σ x‖^2) := by
  obtain ⟨C,hC⟩ := hb
  have hb' : ∀ᵐ x : Configuration n ∂volume, ‖θ x^2‖ ≤ C^2 := by
    exact Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using pow_le_pow_left₀ (abs_nonneg (θ x)) (hC x) 2
  have hh := hi.bdd_mul (hθ.pow 2).aestronglyMeasurable hb'
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  rw [norm_multiplyWavefunction_sq]
  simp only [Pi.pow_apply]
  ring

theorem FormDomain.multiply {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hg : FormDomain ψ g) {θ : Configuration n → ℝ} (hθ : SmoothMultiplier θ) :
    FormDomain (multiplyWavefunction θ ψ) (multiplyGradient θ ψ g) := by
  refine ⟨hg.1.multiply hθ.symmetric,
    hg.2.1.multiply hg.2.2.1 hg.2.2.2.1 hθ.smooth, ?_, ?_, ?_, ?_⟩
  · intro σ
    exact memLp_bounded_real_smul (hg.2.2.1 σ) hθ.smooth.continuous hθ.bounded
  · intro σ i a
    exact (memLp_bounded_real_smul (hg.2.2.1 σ)
      ((hθ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hθ.derivative_bounded i a)).add
      (memLp_bounded_real_smul (hg.2.2.2.1 σ i a) hθ.smooth.continuous hθ.bounded)
  · intro σ i
    exact integrable_weight_multiply hθ.smooth.continuous hθ.bounded ψ σ (hg.2.2.2.2.1 σ i)
  · intro σ i j hij
    exact integrable_weight_multiply hθ.smooth.continuous hθ.bounded ψ σ
      (hg.2.2.2.2.2 σ i j hij)

theorem SmoothMultiplier.const {n : ℕ} (c : ℝ) :
    SmoothMultiplier (fun _ : Configuration n => c) := by
  refine ⟨contDiff_const, fun _ _ => rfl, ⟨|c|, fun _ => le_rfl⟩, ?_⟩
  intro i a
  exact ⟨0, fun x => by simp⟩

theorem SmoothMultiplier.add {n : ℕ} {θ η : Configuration n → ℝ}
    (hθ : SmoothMultiplier θ) (hη : SmoothMultiplier η) :
    SmoothMultiplier (fun x => θ x + η x) := by
  obtain ⟨C,hC⟩ := hθ.bounded
  obtain ⟨D,hD⟩ := hη.bounded
  refine ⟨hθ.smooth.add hη.smooth, fun p x => by rw [hθ.symmetric, hη.symmetric],
    ⟨C+D, fun x => (abs_add_le _ _).trans (add_le_add (hC x) (hD x))⟩, ?_⟩
  intro i a
  obtain ⟨A,hA⟩ := hθ.derivative_bounded i a
  obtain ⟨B,hB⟩ := hη.derivative_bounded i a
  refine ⟨A+B, fun x => ?_⟩
  change |fderiv ℝ (θ + η) x (coordinateDirection i a)| ≤ _
  rw [fderiv_add (hθ.smooth.differentiable (by simp)).differentiableAt
    (hη.smooth.differentiable (by simp)).differentiableAt]
  exact (abs_add_le _ _).trans (add_le_add (hA x) (hB x))

theorem SmoothMultiplier.mul {n : ℕ} {θ η : Configuration n → ℝ}
    (hθ : SmoothMultiplier θ) (hη : SmoothMultiplier η) :
    SmoothMultiplier (fun x => θ x * η x) := by
  obtain ⟨C,hC⟩ := hθ.bounded
  obtain ⟨D,hD⟩ := hη.bounded
  have hC0 : 0 ≤ C := (abs_nonneg (θ 0)).trans (hC 0)
  have hD0 : 0 ≤ D := (abs_nonneg (η 0)).trans (hD 0)
  refine ⟨hθ.smooth.mul hη.smooth, fun p x => by rw [hθ.symmetric, hη.symmetric],
    ⟨C*D, fun x => ?_⟩, ?_⟩
  · rw [abs_mul]
    exact mul_le_mul (hC x) (hD x) (abs_nonneg _) hC0
  · intro i a
    obtain ⟨A,hA⟩ := hθ.derivative_bounded i a
    obtain ⟨B,hB⟩ := hη.derivative_bounded i a
    refine ⟨C*B+D*A, fun x => ?_⟩
    change |fderiv ℝ (θ * η) x (coordinateDirection i a)| ≤ _
    rw [fderiv_mul (hθ.smooth.differentiable (by simp)).differentiableAt
      (hη.smooth.differentiable (by simp)).differentiableAt]
    simp only [add_apply, smul_apply, smul_eq_mul]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul]
    exact add_le_add (mul_le_mul (hC x) (hB x) (abs_nonneg _) hC0)
      (mul_le_mul (hD x) (hA x) (abs_nonneg _) hD0)

theorem FormDomain.scale {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hg : FormDomain ψ g) (c : ℝ) :
    FormDomain (scaleWavefunction c ψ) (scaleGradient c g) := by
  have he : multiplyGradient (fun _ => c) ψ g = scaleGradient c g := by
    funext σ i a x
    simp [multiplyGradient, scaleGradient]
  change FormDomain (multiplyWavefunction (fun _ => c) ψ) (scaleGradient c g)
  rw [← he]
  exact hg.multiply (SmoothMultiplier.const c)

theorem normSquared_scale {n : ℕ} (c : ℝ) (ψ : Wavefunction n) :
    normSquared (scaleWavefunction c ψ) = c^2 * normSquared ψ := by
  simp only [normSquared, scaleWavefunction, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    integral_const_mul, Finset.mul_sum]

theorem energy_scale {n : ℕ} (Z : ℕ) (c : ℝ) (ψ : Wavefunction n) (g : Gradient n) :
    energy Z (scaleWavefunction c ψ) (scaleGradient c g) = c^2 * energy Z ψ g := by
  simp only [energy, scaleWavefunction, scaleGradient, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  simp_rw [← mul_assoc, mul_comm (coulombPotential Z _) (c^2), mul_assoc,
    integral_const_mul, ← Finset.mul_sum]
  ring

theorem normSquared_nonneg {n : ℕ} (ψ : Wavefunction n) : 0 ≤ normSquared ψ :=
  Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _

theorem ae_normSquared_eq_zero {n : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hn : normSquared ψ = 0) (σ : Spins n) :
    (fun x => ‖ψ σ x‖^2) =ᵐ[volume] 0 := by
  have hi : ∫ x : Configuration n, ‖ψ σ x‖^2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun τ _ =>
      integral_nonneg (fun _ => sq_nonneg (‖ψ τ _‖)))).mp hn σ (Finset.mem_univ _)
  exact (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) (hψ σ).norm.integrable_sq).mp hi

theorem energy_nonneg_of_normSquared_zero {n : ℕ} (Z : ℕ)
    {ψ : Wavefunction n} {g : Gradient n} (hd : FormDomain ψ g) (hn : normSquared ψ = 0) :
    0 ≤ energy Z ψ g := by
  have hp : ∀ σ, (∫ x : Configuration n, coulombPotential Z x*‖ψ σ x‖^2) = 0 := by
    intro σ
    have hh := ae_normSquared_eq_zero hd.2.2.1 hn σ
    calc
      _ = ∫ _ : Configuration n, (0 : ℝ) := integral_congr_ae (hh.mono fun x hx => by simp [hx])
      _ = 0 := integral_zero _ _
  simp only [energy, hp, Finset.sum_const_zero, add_zero]
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))))

theorem rayleigh_lower_bound {n : ℕ} (Z : ℕ) {ψ : Wavefunction n} {g : Gradient n}
    (hmin : ∀ (χ : Wavefunction n) (h : Gradient n),
      FormDomain χ h → normSquared χ = 1 → energy Z ψ g ≤ energy Z χ h)
    {χ : Wavefunction n} {h : Gradient n} (hd : FormDomain χ h) :
    energy Z ψ g * normSquared χ ≤ energy Z χ h := by
  rcases (normSquared_nonneg χ).eq_or_lt with hn | hn
  · have hn' : normSquared χ = 0 := hn.symm
    rw [hn', mul_zero]
    exact energy_nonneg_of_normSquared_zero Z hd hn'
  · let c : ℝ := (Real.sqrt (normSquared χ))⁻¹
    have hc : c^2*normSquared χ = 1 := by
      dsimp [c]
      rw [inv_pow, Real.sq_sqrt hn.le, inv_mul_cancel₀ hn.ne']
    have hb := hmin (scaleWavefunction c χ) (scaleGradient c h) (hd.scale c)
      (by rw [normSquared_scale, hc])
    calc
      energy Z ψ g * normSquared χ ≤
          energy Z (scaleWavefunction c χ) (scaleGradient c h) * normSquared χ :=
        mul_le_mul_of_nonneg_right hb hn.le
      _ = energy Z χ h := by
        rw [energy_scale]
        calc
          (c^2*energy Z χ h)*normSquared χ = (c^2*normSquared χ)*energy Z χ h := by ring
          _ = energy Z χ h := by rw [hc, one_mul]

theorem integrable_real_inner_of_memLp {n : ℕ} {f h : Configuration n → ℂ}
    (hf : MemLp f 2 volume) (hh : MemLp h 2 volume) :
    Integrable (fun x => inner ℝ (f x) (h x)) := by
  apply (hf.norm.integrable_sq.add hh.norm.integrable_sq).mono'
    (hf.aestronglyMeasurable.inner hh.aestronglyMeasurable)
  exact Eventually.of_forall fun x => by
    have hb := norm_inner_le_norm (𝕜 := ℝ) (f x) (h x)
    have hs := sq_nonneg (‖f x‖ - ‖h x‖)
    change ‖inner ℝ (f x) (h x)‖ ≤ ‖f x‖^2+‖h x‖^2
    nlinarith [sq_nonneg ‖f x‖, sq_nonneg ‖h x‖]

theorem FormDomain.integrable_potential {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (Z : ℕ) (σ : Spins n) :
    Integrable (fun x : Configuration n => coulombPotential Z x*‖ψ σ x‖^2) := by
  have hn := integrable_finsetSum Finset.univ (fun i _ => hd.2.2.2.2.1 σ i)
  have hp := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum (Finset.univ.filter (fun j : Fin n => i < j))
      (fun j hj => hd.2.2.2.2.2 σ i j (Finset.mem_filter.mp hj).2))
  apply ((hn.const_mul (-(Z:ℝ))).add hp).congr
  exact Eventually.of_forall fun x => by
    simp only [Pi.add_apply, coulombPotential, add_mul, Finset.sum_mul, mul_assoc]

theorem integrable_bounded_mul {n : ℕ} {f θ : Configuration n → ℝ}
    (hf : Integrable f) (hθ : Continuous θ) (hb : ∃ C : ℝ, ∀ x, |θ x| ≤ C) :
    Integrable (fun x => θ x * f x) := by
  obtain ⟨C,hC⟩ := hb
  exact hf.bdd_mul hθ.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hC x)

theorem integral_affine_multiplier_sq {n : ℕ} {f θ : Configuration n → ℝ}
    (hf : Integrable f) (hθ : SmoothMultiplier θ) (t : ℝ) :
    (∫ x, (1+t*θ x)^2*f x) = (∫ x, f x) +
      2*t*(∫ x, θ x*f x) + t^2*(∫ x, θ x^2*f x) := by
  have hi₁ := integrable_bounded_mul hf hθ.smooth.continuous hθ.bounded
  have hi₂ : Integrable (fun x => θ x^2*f x) := by
    simpa only [pow_two] using integrable_bounded_mul hf
      (hθ.mul hθ).smooth.continuous (hθ.mul hθ).bounded
  have he : (fun x => (1+t*θ x)^2*f x) =
      (fun x => f x + (2*t)*(θ x*f x) + t^2*(θ x^2*f x)) := by
    funext x; ring
  have hi₃ : Integrable (fun x => f x+(2*t)*(θ x*f x)) := hf.add (hi₁.const_mul (2*t))
  rw [he, integral_add hi₃ (hi₂.const_mul (t^2)),
    integral_add hf (hi₁.const_mul (2*t)), integral_const_mul, integral_const_mul]

theorem integral_norm_add_smul_sq {n : ℕ} {f h : Configuration n → ℂ}
    (hf : MemLp f 2 volume) (hh : MemLp h 2 volume) (t : ℝ) :
    (∫ x, ‖f x+t • h x‖^2) = (∫ x, ‖f x‖^2) +
      2*t*(∫ x, inner ℝ (f x) (h x)) + t^2*(∫ x, ‖h x‖^2) := by
  have hi := integrable_real_inner_of_memLp hf hh
  have he : (fun x => ‖f x+t • h x‖^2) =
      (fun x => ‖f x‖^2 + (2*t)*(inner ℝ (f x) (h x)) + t^2*‖h x‖^2) := by
    funext x
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  have hi₃ : Integrable (fun x => ‖f x‖^2+(2*t)*(inner ℝ (f x) (h x))) :=
    hf.norm.integrable_sq.add (hi.const_mul (2*t))
  rw [he, integral_add hi₃ (hh.norm.integrable_sq.const_mul (t^2)),
    integral_add hf.norm.integrable_sq (hi.const_mul (2*t)),
    integral_const_mul, integral_const_mul]

theorem multiplyGradient_affine {n : ℕ} {θ : Configuration n → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (ψ : Wavefunction n) (g : Gradient n) (t : ℝ)
    (σ : Spins n) (i : Fin n) (a : Fin 3) (x : Configuration n) :
    multiplyGradient (fun y => 1+t*θ y) ψ g σ i a x =
      g σ i a x + t • multiplyGradient θ ψ g σ i a x := by
  have hd : fderiv ℝ (fun y => 1+t*θ y) x = t • fderiv ℝ θ x := by
    rw [fderiv_const_add, fderiv_const_mul (hθ.differentiable (by simp)).differentiableAt]
  simp only [multiplyGradient, hd, smul_apply, smul_eq_mul,
    Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_one, Complex.real_smul]
  ring

theorem normSquared_affine_multiplier {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) {θ : Configuration n → ℝ} (hθ : SmoothMultiplier θ) (t : ℝ) :
    normSquared (multiplyWavefunction (fun x => 1+t*θ x) ψ) = normSquared ψ +
      2*t*stateWeightedIntegral ψ θ + t^2*normSquared (multiplyWavefunction θ ψ) := by
  simp only [normSquared, norm_multiplyWavefunction_sq, stateWeightedIntegral]
  simp_rw [integral_affine_multiplier_sq (hd.2.2.1 _).norm.integrable_sq hθ,
    Finset.sum_add_distrib, ← Finset.mul_sum]

theorem energy_affine_multiplier {n : ℕ} (Z : ℕ) {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) {θ : Configuration n → ℝ} (hθ : SmoothMultiplier θ) (t : ℝ) :
    energy Z (multiplyWavefunction (fun x => 1+t*θ x) ψ)
      (multiplyGradient (fun x => 1+t*θ x) ψ g) = energy Z ψ g +
      2*t*formMultiplierPairing Z ψ g θ +
        t^2*energy Z (multiplyWavefunction θ ψ) (multiplyGradient θ ψ g) := by
  simp only [energy, formMultiplierPairing, multiplyGradient_affine hθ.smooth,
    norm_multiplyWavefunction_sq]
  simp_rw [integral_norm_add_smul_sq (hd.2.2.2.1 _ _ _) ((hd.multiply hθ).2.2.2.1 _ _ _)]
  have hp : ∀ σ : Spins n, (∫ x : Configuration n,
      coulombPotential Z x*((1+t*θ x)^2*‖ψ σ x‖^2)) =
      (∫ x : Configuration n, coulombPotential Z x*‖ψ σ x‖^2) +
        2*t*(∫ x : Configuration n, θ x*(coulombPotential Z x*‖ψ σ x‖^2)) +
        t^2*(∫ x : Configuration n, coulombPotential Z x*(θ x^2*‖ψ σ x‖^2)) := by
    intro σ
    simpa only [mul_left_comm (coulombPotential Z _)] using
      integral_affine_multiplier_sq (hd.integrable_potential Z σ) hθ t
  simp_rw [hp, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem minimizer_multiplier_pairing {n : ℕ} (Z : ℕ) {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (hn : normSquared ψ = 1)
    (hmin : ∀ (χ : Wavefunction n) (h : Gradient n),
      FormDomain χ h → normSquared χ = 1 → energy Z ψ g ≤ energy Z χ h)
    {θ : Configuration n → ℝ} (hθ : SmoothMultiplier θ) :
    formMultiplierPairing Z ψ g θ = energy Z ψ g * stateWeightedIntegral ψ θ := by
  let P := formMultiplierPairing Z ψ g θ - energy Z ψ g * stateWeightedIntegral ψ θ
  let A := energy Z (multiplyWavefunction θ ψ) (multiplyGradient θ ψ g) -
    energy Z ψ g * normSquared (multiplyWavefunction θ ψ)
  have hb : ∀ t : ℝ, 0 ≤ 2*t*P + t^2*A := by
    intro t
    have hm : SmoothMultiplier (fun x => 1+t*θ x) :=
      (SmoothMultiplier.const 1).add ((SmoothMultiplier.const t).mul hθ)
    have hh := rayleigh_lower_bound Z hmin (hd.multiply hm)
    rw [normSquared_affine_multiplier hd hθ t, energy_affine_multiplier Z hd hθ t, hn] at hh
    dsimp only [P,A]
    nlinarith
  have hlocal : IsLocalMin (fun t : ℝ => 2*t*P+t^2*A) 0 := by
    exact Eventually.of_forall fun t => by simpa using hb t
  have hder : HasDerivAt (fun t : ℝ => 2*t*P+t^2*A) (2*P) 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const P).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const A) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | norm_num
  have he := hlocal.hasDerivAt_eq_zero hder
  dsimp only [P] at he
  linarith

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_ExplicitMultiplyGradient
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

theorem tendsto_integral_bounded_real_smul
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {μ : Measure X}
    {F : ℕ → X → ℝ} {F₀ : X → ℝ} {f : X → E} {C : ℝ}
    (hF : ∀ k, AEStronglyMeasurable (F k) μ)
    (hb : ∀ k x, |F k x| ≤ C) (hf : Integrable f μ)
    (hl : ∀ x, Tendsto (fun k => F k x) atTop (𝓝 (F₀ x))) :
    Tendsto (fun k => ∫ x, F k x • f x ∂μ) atTop
      (𝓝 (∫ x, F₀ x • f x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => C * ‖f x‖)
  · intro k
    exact (hF k).smul hf.aestronglyMeasurable
  · exact hf.norm.const_mul C
  · intro k
    exact Eventually.of_forall fun x => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hb k x) (norm_nonneg _)
  · exact Eventually.of_forall fun x => (hl x).smul tendsto_const_nhds

theorem tendsto_integral_two_bounded_real_smul
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {μ : Measure X}
    {F G : ℕ → X → ℝ} {F₀ G₀ : X → ℝ} {f g : X → E} {C D : ℝ}
    (hF : ∀ k, AEStronglyMeasurable (F k) μ)
    (hG : ∀ k, AEStronglyMeasurable (G k) μ)
    (hbF : ∀ k x, |F k x| ≤ C) (hbG : ∀ k x, |G k x| ≤ D)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hlF : ∀ x, Tendsto (fun k => F k x) atTop (𝓝 (F₀ x)))
    (hlG : ∀ x, Tendsto (fun k => G k x) atTop (𝓝 (G₀ x))) :
    Tendsto (fun k => ∫ x, F k x • f x + G k x • g x ∂μ) atTop
      (𝓝 (∫ x, F₀ x • f x + G₀ x • g x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun x => C * ‖f x‖ + D * ‖g x‖)
  · intro k
    exact ((hF k).smul hf.aestronglyMeasurable).add
      ((hG k).smul hg.aestronglyMeasurable)
  · exact (hf.norm.const_mul C).add (hg.norm.const_mul D)
  · intro k
    exact Eventually.of_forall fun x => by
      calc
        ‖F k x • f x + G k x • g x‖ ≤ ‖F k x • f x‖ + ‖G k x • g x‖ := norm_add_le _ _
        _ ≤ C * ‖f x‖ + D * ‖g x‖ := by
          simp only [norm_smul, Real.norm_eq_abs]
          exact add_le_add
            (mul_le_mul_of_nonneg_right (hbF k x) (norm_nonneg _))
            (mul_le_mul_of_nonneg_right (hbG k x) (norm_nonneg _))
  · exact Eventually.of_forall fun x =>
      ((hlF x).smul tendsto_const_nhds).add ((hlG x).smul tendsto_const_nhds)

theorem HasWeakGradient.multiply_limit {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hg : HasWeakGradient ψ g) (hψ : ∀ σ, MemLp (ψ σ) 2 volume)
    (hgLp : ∀ σ i a, MemLp (g σ i a) 2 volume)
    {θ : Configuration n → ℝ} {Dθ : Fin n → Fin 3 → Configuration n → ℝ}
    {θk : ℕ → Configuration n → ℝ}
    (hθk : ∀ k, ContDiff ℝ ∞ (θk k))
    (hb : ∃ C : ℝ, ∀ k x, |θk k x| ≤ C)
    (hdb : ∀ i a, ∃ C : ℝ, ∀ k x,
      |fderiv ℝ (θk k) x (coordinateDirection i a)| ≤ C)
    (hl : ∀ x, Tendsto (fun k => θk k x) atTop (𝓝 (θ x)))
    (hdl : ∀ i a x, Tendsto
      (fun k => fderiv ℝ (θk k) x (coordinateDirection i a)) atTop (𝓝 (Dθ i a x))) :
    HasWeakGradient (multiplyWavefunction θ ψ) (explicitMultiplyGradient θ Dθ ψ g) := by
  intro σ i a φ hφ hφc
  let dφ : Configuration n → ℝ := fun x => fderiv ℝ φ x (coordinateDirection i a)
  have hdφ : Continuous dφ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφc : HasCompactSupport dφ := hφc.fderiv_apply ℝ _
  obtain ⟨C,hC⟩ := hb
  obtain ⟨B,hB⟩ := hdb i a
  have hi₁ := integrable_test_real_smul (hψ σ) hdφ hdφc
  have hi₂ := integrable_test_real_smul (hψ σ) hφ.continuous hφc
  have hi₃ := integrable_test_real_smul (hgLp σ i a) hφ.continuous hφc
  have hleft := tendsto_integral_bounded_real_smul
    (fun k => (hθk k).continuous.aestronglyMeasurable) hC hi₁ hl
  have hright := tendsto_integral_two_bounded_real_smul
    (fun k => ((hθk k).continuous_fderiv (by simp)).clm_apply continuous_const |>.aestronglyMeasurable)
    (fun k => (hθk k).continuous.aestronglyMeasurable) hB hC hi₂ hi₃ (hdl i a) hl
  have heq : ∀ k,
      (∫ x, θk k x • (dφ x • ψ σ x)) =
      -(∫ x, (fderiv ℝ (θk k) x (coordinateDirection i a)) • (φ x • ψ σ x) +
        θk k x • (φ x • g σ i a x)) := by
    intro k
    have h := hg.multiply hψ hgLp (hθk k) σ i a φ hφ hφc
    change (∫ x, dφ x • (θk k x • ψ σ x)) =
      -(∫ x, φ x • ((fderiv ℝ (θk k) x (coordinateDirection i a)) • ψ σ x +
        θk k x • g σ i a x)) at h
    simpa only [smul_add, smul_smul, mul_comm] using h
  have ht := tendsto_nhds_unique hleft (hright.neg.congr' (Eventually.of_forall fun k => (heq k).symm))
  change (∫ x, dφ x • (θ x • ψ σ x)) =
    -(∫ x, φ x • (Dθ i a x • ψ σ x + θ x • g σ i a x))
  simpa only [smul_add, smul_smul, mul_comm] using ht

theorem memLp_bounded_measurable_real_smul {n : ℕ} {f : Configuration n → ℂ}
    (hf : MemLp f 2 volume) {θ : Configuration n → ℝ}
    (hθ : AEStronglyMeasurable θ volume)
    (hb : ∃ C : ℝ, ∀ x, |θ x| ≤ C) : MemLp (fun x => θ x • f x) 2 volume := by
  obtain ⟨C,hC⟩ := hb
  apply hf.of_le_mul (c := C) (hθ.smul hf.aestronglyMeasurable)
  exact Eventually.of_forall fun x => by
    change ‖θ x • f x‖ ≤ C * ‖f x‖
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

theorem FormDomain.multiply_limit {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hg : FormDomain ψ g)
    {θ : Configuration n → ℝ} {Dθ : Fin n → Fin 3 → Configuration n → ℝ}
    {θk : ℕ → Configuration n → ℝ}
    (hθ : Continuous θ) (hsym : ∀ (p : Equiv.Perm (Fin n)) x, θ (x ∘ p) = θ x)
    (hD : ∀ i a, AEStronglyMeasurable (Dθ i a) volume)
    (hθk : ∀ k, ContDiff ℝ ∞ (θk k))
    (hb : ∃ C : ℝ, ∀ k x, |θk k x| ≤ C)
    (hdb : ∀ i a, ∃ C : ℝ, ∀ k x,
      |fderiv ℝ (θk k) x (coordinateDirection i a)| ≤ C)
    (hl : ∀ x, Tendsto (fun k => θk k x) atTop (𝓝 (θ x)))
    (hdl : ∀ i a x, Tendsto
      (fun k => fderiv ℝ (θk k) x (coordinateDirection i a)) atTop (𝓝 (Dθ i a x))) :
    FormDomain (multiplyWavefunction θ ψ) (explicitMultiplyGradient θ Dθ ψ g) := by
  have hbθ : ∃ C : ℝ, ∀ x, |θ x| ≤ C := by
    obtain ⟨C,hC⟩ := hb
    exact ⟨C, fun x => le_of_tendsto (hl x).abs (Eventually.of_forall fun k => hC k x)⟩
  have hbD : ∀ i a, ∃ C : ℝ, ∀ x, |Dθ i a x| ≤ C := by
    intro i a
    obtain ⟨C,hC⟩ := hdb i a
    exact ⟨C, fun x => le_of_tendsto (hdl i a x).abs (Eventually.of_forall fun k => hC k x)⟩
  refine ⟨hg.1.multiply hsym,
    hg.2.1.multiply_limit hg.2.2.1 hg.2.2.2.1 hθk hb hdb hl hdl, ?_, ?_, ?_, ?_⟩
  · intro σ
    exact memLp_bounded_real_smul (hg.2.2.1 σ) hθ hbθ
  · intro σ i a
    exact (memLp_bounded_measurable_real_smul (hg.2.2.1 σ) (hD i a) (hbD i a)).add
      (memLp_bounded_real_smul (hg.2.2.2.1 σ i a) hθ hbθ)
  · intro σ i
    exact integrable_weight_multiply hθ hbθ ψ σ (hg.2.2.2.2.1 σ i)
  · intro σ i j hij
    exact integrable_weight_multiply hθ hbθ ψ σ (hg.2.2.2.2.2 σ i j hij)

theorem energy_localization_explicit {n : ℕ} (Z : ℕ) {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) {θ : Configuration n → ℝ}
    {Dθ : Fin n → Fin 3 → Configuration n → ℝ}
    (hsq : SmoothMultiplier (fun x => θ x^2))
    (hD : ∀ i a, AEStronglyMeasurable (Dθ i a) volume)
    (hDb : ∀ i a, ∃ C : ℝ, ∀ x, |Dθ i a x| ≤ C)
    (hrel : ∀ i a x, fderiv ℝ (fun y => θ y^2) x (coordinateDirection i a) =
      2*θ x*Dθ i a x) :
    energy Z (multiplyWavefunction θ ψ) (explicitMultiplyGradient θ Dθ ψ g) =
      formMultiplierPairing Z ψ g (fun x => θ x^2) + explicitLocalizationError ψ Dθ := by
  have hpw : ∀ σ i a x, ‖explicitMultiplyGradient θ Dθ ψ g σ i a x‖^2 =
      inner ℝ (g σ i a x) (multiplyGradient (fun y => θ y^2) ψ g σ i a x) +
      (Dθ i a x)^2*‖ψ σ x‖^2 := by
    intro σ i a x
    simp only [explicitMultiplyGradient, multiplyGradient, hrel, norm_add_sq_real, norm_smul,
      inner_add_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [real_inner_comm (ψ σ x) (g σ i a x)]
    ring
  have herr : ∀ σ i a, Integrable (fun x : Configuration n => (Dθ i a x)^2*‖ψ σ x‖^2) := by
    intro σ i a
    have hl := memLp_bounded_measurable_real_smul (hd.2.2.1 σ) (hD i a) (hDb i a)
    simpa only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] using hl.norm.integrable_sq
  have hi : ∀ σ i a, (∫ x : Configuration n, ‖explicitMultiplyGradient θ Dθ ψ g σ i a x‖^2) =
      (∫ x : Configuration n,
        inner ℝ (g σ i a x) (multiplyGradient (fun y => θ y^2) ψ g σ i a x)) +
      ∫ x : Configuration n, (Dθ i a x)^2*‖ψ σ x‖^2 := by
    intro σ i a
    simp_rw [hpw]
    exact integral_add (integrable_real_inner_of_memLp (hd.2.2.2.1 σ i a)
      ((hd.multiply hsq).2.2.2.1 σ i a)) (herr σ i a)
  simp only [energy, formMultiplierPairing, explicitLocalizationError, hi,
    norm_multiplyWavefunction_sq, Finset.sum_add_distrib, mul_left_comm (coulombPotential Z _)]
  ring

open scoped ENNReal Convolution

theorem observationNoiseDensity_contDiff : ContDiff ℝ ∞ observationNoiseDensity :=
  contDiff_const.mul observationNoiseBase_contDiff

theorem observationNoiseDensity_formula (u : ℝ) :
    observationNoiseDensity u = observationNoiseNormalizer*
      (if |u| < 1 then Real.exp (-(1-u^2)⁻¹) else 0) := by
  rw [observationNoiseDensity, observationNoiseBase_formula]

theorem observationTranslationScore_measurable : Measurable observationTranslationScore := by
  unfold observationTranslationScore
  fun_prop

theorem observationNoiseDensity_even (u : ℝ) :
    observationNoiseDensity (-u) = observationNoiseDensity u := by
  simp [observationNoiseDensity, observationNoiseBase]

theorem observationTranslationScore_odd (u : ℝ) :
    observationTranslationScore (-u) = -observationTranslationScore u := by
  simp [observationTranslationScore, neg_div]

theorem observationNoiseDensity_hasDerivAt (u : ℝ) :
    HasDerivAt observationNoiseDensity
      (-observationTranslationScore u * observationNoiseDensity u) u := by
  have hg : HasDerivAt expNegInvGlue
      ((1-u^2)⁻¹ ^ 2 * expNegInvGlue (1-u^2)) (1-u^2) := by
    simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) (1-u^2)
  have hi : HasDerivAt (fun v : ℝ => 1-v^2) (-2*u) u := by
    convert! (hasDerivAt_pow 2 u).const_sub 1 using 1
    all_goals try with_reducible_and_instances rfl
    ring
  convert! (hg.comp u hi).const_mul observationNoiseNormalizer using 1
  all_goals try with_reducible_and_instances rfl
  simp only [observationNoiseDensity, observationNoiseBase, observationTranslationScore,
    div_eq_mul_inv, inv_pow]
  ring

theorem pow_mul_exp_neg_le_factorial (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    t^k * Real.exp (-t) ≤ (k.factorial : ℝ) := by
  have hk : (0:ℝ) < k.factorial := by positivity
  have h := (div_le_iff₀ hk).mp (Real.pow_div_factorial_le_exp t ht k)
  have hh := mul_le_mul_of_nonneg_right h (Real.exp_pos (-t)).le
  simpa [Real.exp_neg, mul_assoc, mul_left_comm, mul_comm] using hh

theorem observationScore_weighted_pow_bound (q : ℕ) (u : ℝ) :
    |observationTranslationScore u|^q * observationNoiseDensity u ≤
      (Set.Icc (-1:ℝ) 1).indicator
        (fun _ => observationNoiseNormalizer * 2^q * ((2*q).factorial : ℝ)) u := by
  classical
  have hc : 0 ≤ observationNoiseNormalizer :=
    inv_nonneg.mpr observationNoiseBase_integral_pos.le
  by_cases hu : |u| < 1
  · have hb : u ∈ Set.Icc (-1:ℝ) 1 :=
      ⟨(abs_lt.mp hu).1.le, (abs_lt.mp hu).2.le⟩
    rw [Set.indicator_of_mem hb, observationNoiseDensity_formula, ite_eq_left hu]
    have hv : 0 < 1-u^2 := sub_pos.mpr ((sq_lt_one_iff_abs_lt_one u).mpr hu)
    have hs : |observationTranslationScore u| ≤ 2 * ((1-u^2)⁻¹)^2 := by
      unfold observationTranslationScore
      rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_pow, abs_of_pos hv]
      rw [div_eq_mul_inv, inv_pow]
      nlinarith [mul_le_mul_of_nonneg_right hu.le
        (inv_nonneg.mpr (sq_nonneg (1-u^2)))]
    calc
      |observationTranslationScore u|^q *
          (observationNoiseNormalizer * Real.exp (-(1-u^2)⁻¹)) ≤
          (2 * ((1-u^2)⁻¹)^2)^q *
            (observationNoiseNormalizer * Real.exp (-(1-u^2)⁻¹)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hs q)
          (mul_nonneg hc (Real.exp_pos _).le)
      _ = (observationNoiseNormalizer * 2^q) *
          (((1-u^2)⁻¹)^(2*q) * Real.exp (-(1-u^2)⁻¹)) := by
        rw [mul_pow, pow_mul]; ring
      _ ≤ (observationNoiseNormalizer * 2^q) * ((2*q).factorial : ℝ) :=
        mul_le_mul_of_nonneg_left
          (pow_mul_exp_neg_le_factorial (2*q) (inv_nonneg.mpr hv.le))
          (mul_nonneg hc (by positivity))
  · rw [observationNoiseDensity_formula, ite_eq_right hu]
    simp only [mul_zero]
    exact Set.indicator_nonneg (fun _ _ => by positivity) u

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_CutJensen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

theorem conditional_ensemble_positive_jensen {P : Type*} [Fintype P]
    (m k : P → ℕ) (u : (p : P) → H1Vector (m p+k p))
    (W : (p : P) → Configuration (m p+k p) → ℝ)
    (hW : ∀ p, Measurable (W p)) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ p x, |W p x| ≤ B) (hmass : (∑ p, mass (u p))=1) :
    (max (∑ p, potentialForm (W p) (u p)) 0)^2 ≤
      ∑ p, sliceExpectation (u p) (fun s x => (max (coreConditionalObservable (u p) (W p) s x) 0)^2) := by
  let F := fun p => coreConditionalObservable (u p) (W p)
  let c : ℝ := ∑ p, sliceExpectation (u p) (fun s x => max (F p s x) 0)
  have hp (p) (s : Spins (m p)) : Integrable (fun x => mass ((u p).coreSlice s x)*max (F p s x) 0) := by
    simpa only [pow_one] using coreConditionalObservable_positive_weight_integrable (u p) (W p) (hW p) hB0 (hB p) s 1
  have hq (p) (s : Spins (m p)) := coreConditionalObservable_positive_weight_integrable (u p) (W p) (hW p) hB0 (hB p) s 2
  have hc0 : 0 ≤ c := Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun s _ =>
    integral_nonneg (fun x => mul_nonneg (mass_nonneg _) (le_max_right _ _))))
  have hc : max (∑ p, potentialForm (W p) (u p)) 0 ≤ c := by
    apply max_le _ hc0
    apply Finset.sum_le_sum
    intro p _
    rw [←sliceExpectation_coreConditionalObservable (u p) (W p) (hW p) (hB p)]
    apply Finset.sum_le_sum
    intro s _
    exact integral_mono (coreConditionalObservable_weight_integrable (u p) (W p) (hW p) hB0 (hB p) s)
      (hp p s) (fun x => mul_le_mul_of_nonneg_left (le_max_left _ _) (mass_nonneg _))
  have hn : 0 ≤ ∑ p, ∑ s : Spins (m p), ∫ x, mass ((u p).coreSlice s x)*(max (F p s x) 0-c)^2 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => mul_nonneg (mass_nonneg _) (sq_nonneg _))))
  have he (p) (s : Spins (m p)) :
      (∫ x, mass ((u p).coreSlice s x)*(max (F p s x) 0-c)^2) =
      (∫ x, mass ((u p).coreSlice s x)*(max (F p s x) 0)^2)-
      2*c*(∫ x, mass ((u p).coreSlice s x)*max (F p s x) 0)+
      c^2*(∫ x, mass ((u p).coreSlice s x)) := by
    have hi : Integrable (fun x => mass ((u p).coreSlice s x)*(max (F p s x) 0)^2-
        (2*c)*(mass ((u p).coreSlice s x)*max (F p s x) 0)) := by
      exact (hq p s).sub ((hp p s).const_mul (2*c))
    calc
      _ = ∫ x, (mass ((u p).coreSlice s x)*(max (F p s x) 0)^2-
          (2*c)*(mass ((u p).coreSlice s x)*max (F p s x) 0))+c^2*mass ((u p).coreSlice s x) :=
        integral_congr_ae (Eventually.of_forall (fun x => by ring))
      _ = _ := by rw [integral_add hi ((mass_coreSlice_integrable (u p) s).const_mul _),
        integral_sub (hq p s) ((hp p s).const_mul _),integral_const_mul,integral_const_mul]
  simp only [he,Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,integral_mass_coreSlice,hmass,mul_one] at hn
  change 0 ≤ (∑ p, sliceExpectation (u p) (fun s x => (max (F p s x) 0)^2))-2*c*c+c^2 at hn
  have H := pow_le_pow_left₀ (le_max_right (∑ p, potentialForm (W p) (u p)) 0) hc 2
  dsimp [F] at hn
  nlinarith

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_CorrectionDensity
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom
open scoped Convolution
open ContinuousLinearMap

theorem potentialOf_nonneg {ρ : Position → ℝ} (hρ : ∀ y, 0 ≤ ρ y) (x : Position) :
    0 ≤ potentialOf ρ x := integral_nonneg (fun y => mul_nonneg (coulombKernel_nonneg _) (hρ y))

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_UniformScreening
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

theorem AtomicBudgetHistory.universal_positive_field {J n j : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hψ : Antisymmetric ψ) (hm : mass ψ=1)
    {E δ a B : ℝ} (hE : (E:EReal) ≤ unrestrictedFormBottom S) (hstate : form S ψ ≤ E+δ)
    (hB : B ≤ atomicCountConstant*screenEnergy δ a) (hδ : 0 ≤ δ) (ha : 0 < a)
    (T : AtomicBudgetHistory S ψ B j) (hT : ∀ i, AtomicScaleWindow a (4^j) (T.target i))
    (y : Space) (hy : AtomicScaleWindow a (4^j) y) :
    Real.sqrt (T.ensemble.rawSquare S y (atomicCellScale y)) ≤
      2*atomicBudgetRecursionC^(j+2)*screenFieldUnit δ atomicCountConstant a := by
  apply T.positive_field S hatom ψ hm hE hstate hB hδ
    (by linarith [atomicCountConstant_ge_two]) ha _ hT y hy
  intro z hz
  exact (screenCountParameter_controls ψ hm δ hz).trans
    (mul_le_mul_of_nonneg_right (screenCountParameter_le_atomicCountConstant S hatom ψ hψ hm hE hstate hδ) (sq_nonneg _))

lemma RecordedEnsemble.mean_raw_le_sqrt {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n)
    (hm : mass ψ=1) (T : RecordedEnsemble n) (hT : T.Conserves ψ)
    (hTm : T.totalMass=mass ψ) (y : Space) {a : ℝ} (ha : 0 < a) :
    max (attraction S y-restrictedCorePotential ψ {z | 40*a ≤ ‖z-y‖} y) 0 ≤
      Real.sqrt (T.rawSquare S y a) := by
  let A : Set Space := {z | 40*a ≤ ‖z-y‖}
  have hA : MeasurableSet A := (isClosed_le continuous_const (by fun_prop)).measurableSet
  let W : Configuration n → ℝ := rawSignedField (attraction S y) A y
  have hW : Measurable W := rawSignedField_measurable _ hA y
  let B : ℝ := |attraction S y|+(n:ℝ)/(40*a)
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hB : ∀ x, |W x| ≤ B := rawSignedField_abs_le _ _ y (by positivity) (fun _ h => h)
  have hcons := hT W hW ⟨B,hB⟩
  have hreindex (p) (x : Configuration (T.out p+T.core p)) :
      W (reindexConfiguration (T.labels p) x)=rawSignedField (attraction S y) A y x :=
    rawSignedField_reindex _ _ _ _ _
  have H := conditional_ensemble_positive_jensen T.out T.core T.vector
    (fun p x => W (reindexConfiguration (T.labels p) x))
    (fun p => by simpa only [hreindex] using (rawSignedField_measurable (n:=T.out p+T.core p) (attraction S y) hA y))
    hB0 (fun p x => hB _) (hTm.trans hm)
  change (max (∑ p, potentialForm (W ∘ reindexConfiguration (T.labels p)) (T.vector p)) 0)^2 ≤ _ at H
  rw [hcons,potentialForm_rawSignedField ψ _ hA y (by positivity) (fun _ h => h),hm,mul_one] at H
  simp_rw [hreindex] at H
  exact (Real.le_sqrt (le_max_right _ _) (T.rawSquare_nonneg S y a)).mpr H

theorem atomic_expected_raw_field_bound {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hψ : Antisymmetric ψ) (hm : mass ψ=1)
    {E δ : ℝ} (hE : (E:EReal) ≤ unrestrictedFormBottom S) (hstate : form S ψ ≤ E+δ)
    (hδ : 0 ≤ δ) {y : Space} (hy : y≠0) :
    max (attraction S y-restrictedCorePotential ψ {z | 40*atomicCellScale y ≤ ‖z-y‖} y) 0 ≤
      2*atomicBudgetRecursionC^2*screenFieldUnit δ atomicCountConstant (atomicCellScale y) := by
  let T := AtomicBudgetHistory.initial S ψ hψ
  have ha := atomicCellScale_pos hy
  have hB : (0:ℝ) ≤ atomicCountConstant*screenEnergy δ (atomicCellScale y) :=
    mul_nonneg (by linarith [atomicCountConstant_ge_two]) (div_nonneg (sq_nonneg _) ha.le)
  have H := T.universal_positive_field S hatom ψ hψ hm hE hstate hB hδ ha
    (fun i => Fin.elim0 i) y (by simp only [pow_zero,AtomicScaleWindow,one_mul,le_refl,and_self])
  exact (T.ensemble.mean_raw_le_sqrt S ψ hm T.law T.mass_eq y ha).trans H

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_SignAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
open scoped ENNReal Convolution

theorem observationScore_weighted_pow_integrable (q : ℕ) :
    Integrable (fun u : ℝ => |observationTranslationScore u|^q *
      observationNoiseDensity u) := by
  have hi : Integrable ((Set.Icc (-1:ℝ) 1).indicator
      (fun _ => observationNoiseNormalizer * 2^q * ((2*q).factorial : ℝ))) := by
    exact (integrableOn_const (by norm_num : (volume (Set.Icc (-1:ℝ) 1)) ≠ (⊤ : ℝ≥0∞))).integrable_indicator
      measurableSet_Icc
  apply hi.mono' ((observationTranslationScore_measurable.abs.pow_const q).mul
    observationNoiseDensity_contDiff.continuous.measurable).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun u => by
    change ‖|observationTranslationScore u|^q * observationNoiseDensity u‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (pow_nonneg (abs_nonneg _) _) (observationNoiseDensity_nonneg u))]
    exact observationScore_weighted_pow_bound q u

theorem observationNoise_integral (f : ℝ → ℝ) :
    (∫ u, f u ∂observationNoiseLaw) =
      ∫ u, observationNoiseDensity u * f u := by
  rw [observationNoiseLaw, integral_withDensity_eq_integral_toReal_smul]
  · simp only [ENNReal.toReal_ofReal (observationNoiseDensity_nonneg _), smul_eq_mul]
  · exact observationNoiseDensity_contDiff.continuous.measurable.ennreal_ofReal
  · exact Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

theorem observationScore_pow_integrable (q : ℕ) :
    Integrable (fun u => |observationTranslationScore u|^q) observationNoiseLaw := by
  rw [observationNoiseLaw, integrable_withDensity_iff_integrable_smul']
  · simpa only [ENNReal.toReal_ofReal (observationNoiseDensity_nonneg _),
      smul_eq_mul, mul_comm] using observationScore_weighted_pow_integrable q
  · exact observationNoiseDensity_contDiff.continuous.measurable.ennreal_ofReal
  · exact Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

theorem observationScore_moment_le_factorial (q : ℕ) :
    (∫ u, |observationTranslationScore u|^q ∂observationNoiseLaw) ≤
      2 * observationNoiseNormalizer * 2^q * ((2*q).factorial : ℝ) := by
  classical
  have hi : Integrable ((Set.Icc (-1:ℝ) 1).indicator
      (fun _ => observationNoiseNormalizer * 2^q * ((2*q).factorial : ℝ))) := by
    exact (integrableOn_const (by norm_num : (volume (Set.Icc (-1:ℝ) 1)) ≠
      (⊤ : ℝ≥0∞))).integrable_indicator measurableSet_Icc
  rw [observationNoise_integral]
  have h := integral_mono (observationScore_weighted_pow_integrable q) hi
    (observationScore_weighted_pow_bound q)
  rw [integral_indicator measurableSet_Icc] at h
  simpa [mul_comm, mul_left_comm, mul_assoc, Measure.real, Real.volume_Icc, show (1+1:ℝ)=2 by norm_num] using h

theorem observationScore_moment_le_pow (q : ℕ) (hq : 1 ≤ q) :
    (∫ u, |observationTranslationScore u|^q ∂observationNoiseLaw) ≤
      (8 * max 1 (2 * observationNoiseNormalizer) * (q:ℝ)^2)^q := by
  let B : ℝ := max 1 (2 * observationNoiseNormalizer)
  have hB : 1 ≤ B := le_max_left _ _
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hBp : 2 * observationNoiseNormalizer ≤ B^q := by
    have hh : B^1 ≤ B^q := pow_le_pow_right₀ hB hq
    exact (show 2 * observationNoiseNormalizer ≤ B from le_max_right _ _).trans
      (by simpa only [pow_one] using hh)
  have hc : 0 ≤ observationNoiseNormalizer :=
    inv_nonneg.mpr observationNoiseBase_integral_pos.le
  have hfac : ((2*q).factorial : ℝ) ≤ (2*(q:ℝ))^(2*q) := by
    exact_mod_cast Nat.factorial_le_pow (2*q)
  calc
    (∫ u, |observationTranslationScore u|^q ∂observationNoiseLaw) ≤
        2 * observationNoiseNormalizer * 2^q * ((2*q).factorial : ℝ) :=
      observationScore_moment_le_factorial q
    _ ≤ B^q * 2^q * (2*(q:ℝ))^(2*q) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hBp (by positivity)) hfac
        (by positivity) (by positivity)
    _ = (8 * B * (q:ℝ)^2)^q := by
      rw [pow_mul, ← mul_pow, ← mul_pow]
      congr 1
      ring

open scoped BigOperators

theorem signAverage_const {ι : Type*} [Fintype ι] (c : ℝ) :
    signAverage (ι := ι) (fun _ => c) = c := by
  classical
  unfold signAverage
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

theorem signAverage_mono {ι : Type*} [Fintype ι] {f g : (ι → Bool) → ℝ}
    (hfg : ∀ ε, f ε ≤ g ε) : signAverage f ≤ signAverage g := by
  classical
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ε _ => hfg ε) (by positivity)

theorem signAverage_add {ι : Type*} [Fintype ι] (f g : (ι → Bool) → ℝ) :
    signAverage (fun ε => f ε + g ε) = signAverage f + signAverage g := by
  classical
  simp [signAverage, Finset.sum_add_distrib, mul_add]

theorem signAverage_const_mul {ι : Type*} [Fintype ι] (c : ℝ) (f : (ι → Bool) → ℝ) :
    signAverage (fun ε => c * f ε) = c * signAverage f := by
  classical
  simp [signAverage, ← Finset.mul_sum, mul_left_comm]

theorem signAverage_prod {ι : Type*} [Fintype ι] (f : ι → Bool → ℝ) :
    signAverage (fun ε => ∏ i, f i (ε i)) =
      ∏ i, ((f i false + f i true) / 2) := by
  classical
  unfold signAverage
  rw [← Fintype.prod_sum]
  simp only [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat,
    Fintype.sum_bool, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
  simp [div_eq_mul_inv, mul_comm, add_comm]

theorem signAverage_exp_sum {ι : Type*} [Fintype ι] (c : ι → ℝ) (t : ℝ) :
    signAverage (fun ε => Real.exp (t * ∑ i, boolSign (ε i) * c i)) ≤
      Real.exp (t^2 * (∑ i, (c i)^2) / 2) := by
  classical
  have he : (fun ε : ι → Bool => Real.exp (t * ∑ i, boolSign (ε i) * c i)) =
      (fun ε : ι → Bool => ∏ i, Real.exp (t * (boolSign (ε i) * c i))) := by
    funext ε
    rw [Finset.mul_sum, Real.exp_sum]
  rw [he, signAverage_prod (fun i b => Real.exp (t * (boolSign b * c i)))]
  have hc : ∀ i, (Real.exp (t * (boolSign false * c i)) +
      Real.exp (t * (boolSign true * c i))) / 2 = Real.cosh (t * c i) := by
    intro i
    simp [boolSign, Real.cosh_eq, add_comm]
  simp_rw [hc]
  calc
    ∏ i, Real.cosh (t*c i) ≤ ∏ i, Real.exp ((t*c i)^2/2) :=
      Finset.prod_le_prod (fun index _ => (Real.cosh_pos (t * c index)).le)
        (fun index _ => Real.cosh_le_exp_half_sq (t * c index))
    _ = Real.exp (t^2 * (∑ i, (c i)^2) / 2) := by
      rw [← Real.exp_sum]
      congr 1
      simp_rw [mul_pow, div_eq_mul_inv, ← Finset.sum_mul, ← Finset.mul_sum]

theorem even_pow_le_factorial_exp (x : ℝ) (k : ℕ) :
    x^(2*k) ≤ ((2*k).factorial : ℝ) * (Real.exp x + Real.exp (-x)) := by
  have hf : (0:ℝ) < (2*k).factorial := by positivity
  by_cases hx : 0 ≤ x
  · have h := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp x hx (2*k))
    nlinarith [Real.exp_pos (-x)]
  · have h := (div_le_iff₀ hf).mp
      (Real.pow_div_factorial_le_exp (-x) (by linarith) (2*k))
    rw [pow_mul, neg_sq, ← pow_mul] at h
    nlinarith [Real.exp_pos x]

theorem signAverage_scaled_even_pow_le {ι : Type*} [Fintype ι]
    (f : (ι → Bool) → ℝ) {A : ℝ}
    (hf : ∀ t : ℝ, signAverage (fun ε => Real.exp (t * f ε)) ≤ Real.exp (t^2*A/2))
    (t : ℝ) (k : ℕ) :
    t^(2*k) * signAverage (fun ε => (f ε)^(2*k)) ≤
      2 * ((2*k).factorial : ℝ) * Real.exp (t^2*A/2) := by
  calc
    t^(2*k) * signAverage (fun ε => (f ε)^(2*k)) =
        signAverage (fun ε => (t * f ε)^(2*k)) := by
      simp_rw [mul_pow, signAverage_const_mul]
    _ ≤ signAverage (fun ε => ((2*k).factorial : ℝ) *
        (Real.exp (t * f ε) + Real.exp (-(t * f ε)))) :=
      signAverage_mono fun ε => even_pow_le_factorial_exp (t*f ε) k
    _ = ((2*k).factorial : ℝ) *
        (signAverage (fun ε => Real.exp (t*f ε)) +
          signAverage (fun ε => Real.exp ((-t)*f ε))) := by
      rw [signAverage_const_mul, signAverage_add]
      simp only [neg_mul]
    _ ≤ ((2*k).factorial : ℝ) *
        (Real.exp (t^2*A/2) + Real.exp ((-t)^2*A/2)) :=
      mul_le_mul_of_nonneg_left (add_le_add (hf t) (hf (-t))) (by positivity)
    _ = 2 * ((2*k).factorial : ℝ) * Real.exp (t^2*A/2) := by rw [neg_sq]; ring

theorem signAverage_even_pow_le_of_exp {ι : Type*} [Fintype ι]
    (f : (ι → Bool) → ℝ) {A : ℝ} (hA : 0 < A)
    (hf : ∀ t : ℝ, signAverage (fun ε => Real.exp (t*f ε)) ≤ Real.exp (t^2*A/2))
    (k : ℕ) (hk : 0 < k) :
    signAverage (fun ε => (f ε)^(2*k)) ≤
      2 * (2*(k:ℝ)*Real.exp 1)^k * A^k := by
  have hq : 0 < 2*(k:ℝ) := by positivity
  let t : ℝ := Real.sqrt (2*(k:ℝ)/A)
  have ht : t^2 = 2*(k:ℝ)/A := Real.sq_sqrt (by positivity)
  have hte : t^2*A/2 = (k:ℝ) := by rw [ht]; field_simp
  have hr := signAverage_scaled_even_pow_le f hf t k
  rw [show t^(2*k) = (2*(k:ℝ)/A)^k by rw [pow_mul, ht], hte] at hr
  have hfac : ((2*k).factorial : ℝ) ≤ (2*(k:ℝ))^(2*k) := by
    exact_mod_cast Nat.factorial_le_pow (2*k)
  have hek : Real.exp (k:ℝ) = (Real.exp 1)^k := by
    simpa only [mul_one] using Real.exp_nat_mul 1 k
  apply (mul_le_mul_iff_left₀ (pow_pos hq k)).mp
  calc
    signAverage (fun ε => (f ε)^(2*k)) * (2*(k:ℝ))^k =
        ((2*(k:ℝ)/A)^k * signAverage (fun ε => (f ε)^(2*k))) * A^k := by
      rw [mul_right_comm, ← mul_pow, div_mul_cancel₀ _ hA.ne']
      ring
    _ ≤ (2 * ((2*k).factorial : ℝ) * Real.exp (k:ℝ)) * A^k :=
      mul_le_mul_of_nonneg_right hr (pow_nonneg hA.le k)
    _ ≤ (2 * (2*(k:ℝ))^(2*k) * Real.exp (k:ℝ)) * A^k := by
      gcongr
    _ = (2 * (2*(k:ℝ)*Real.exp 1)^k * A^k) * (2*(k:ℝ))^k := by
      rw [hek, show (2*(k:ℝ))^(2*k) = ((2*(k:ℝ))^k)^2 by rw [← pow_mul]; congr 1; omega]
      rw [mul_pow]
      ring

theorem signAverage_sum_even_pow {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (k : ℕ) (hk : 0 < k) :
    signAverage (fun ε => (∑ i, boolSign (ε i) * c i)^(2*k)) ≤
      2 * (2*(k:ℝ)*Real.exp 1)^k * (∑ i, (c i)^2)^k := by
  classical
  have hA : 0 ≤ ∑ i, (c i)^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rcases hA.eq_or_lt with hzero | hpos
  · have hc : ∀ i, c i = 0 := by
      intro i
      have hh : (c i)^2 ≤ ∑ i, (c i)^2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      rw [← hzero] at hh
      nlinarith [sq_nonneg (c i)]
    simp [hc, show 2*k ≠ 0 by omega, hk.ne', signAverage_const]
  · exact signAverage_even_pow_le_of_exp _ hpos (signAverage_exp_sum c) k hk

instance observationNoiseLaw_negInvariant : observationNoiseLaw.IsNegInvariant := by
  constructor
  ext s hs
  change (Measure.map (fun u : ℝ => -u) observationNoiseLaw) s = observationNoiseLaw s
  rw [Measure.map_apply measurable_neg hs]
  unfold observationNoiseLaw
  rw [withDensity_apply _ (measurable_neg hs), withDensity_apply _ hs,
    ← lintegral_indicator (measurable_neg hs), ← lintegral_indicator hs]
  have h := lintegral_neg_eq_self (μ := (volume : Measure ℝ))
    (s.indicator (fun u => ENNReal.ofReal (observationNoiseDensity u)))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext u
  classical
  by_cases hu : -u ∈ s <;> simp [hu, observationNoiseDensity_even]

theorem observationNoisePi_sign_preserving {ι : Type*} [Fintype ι] (ε : ι → Bool) :
    MeasurePreserving (fun u : ι → ℝ => fun i => boolSign (ε i) * u i)
      (Measure.pi fun _ : ι => observationNoiseLaw)
      (Measure.pi fun _ : ι => observationNoiseLaw) := by
  have hs (b : Bool) : MeasurePreserving (fun u : ℝ => boolSign b * u)
      observationNoiseLaw observationNoiseLaw := by
    cases b
    · simpa [boolSign] using observationNoiseLaw.measurePreserving_neg
    · convert! (MeasurePreserving.id observationNoiseLaw) using 1
      all_goals try with_reducible_and_instances rfl
      ext u
      simp [boolSign]
  refine ⟨Measurable.of_eval (fun index => measurable_const.mul (measurable_pi_apply index)), ?_⟩
  rw [Measure.pi_map_pi (fun i => (hs (ε i)).measurable.aemeasurable)]
  simp_rw [(hs _).map_eq]

theorem observationScore_memLp (q : ℕ) (hq : q ≠ 0) :
    MemLp observationTranslationScore (q : ℝ≥0∞) observationNoiseLaw := by
  apply (integrable_norm_rpow_iff
    observationTranslationScore_measurable.aestronglyMeasurable
    (by exact_mod_cast hq) (by simp)).mp
  simpa using observationScore_pow_integrable q

theorem observationScorePi_sum_memLp {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (q : ℕ) (hq : q ≠ 0) :
    MemLp (fun u : ι → ℝ => ∑ i, a i * observationTranslationScore (u i))
      (q : ℝ≥0∞) (Measure.pi fun _ : ι => observationNoiseLaw) := by
  classical
  apply memLp_finsetSum
  intro i _
  exact ((observationScore_memLp q hq).comp_measurePreserving
    (measurePreserving_eval (fun _ : ι => observationNoiseLaw) i)).const_mul (a i)

theorem observationScorePi_sum_pow_integrable {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (q : ℕ) (hq : q ≠ 0) :
    Integrable (fun u : ι → ℝ => |∑ i, a i * observationTranslationScore (u i)|^q)
      (Measure.pi fun _ : ι => observationNoiseLaw) := by
  simpa only [Real.norm_eq_abs] using
    (observationScorePi_sum_memLp a q hq).integrable_norm_pow hq

theorem weighted_sum_pow_le {ι : Type*} [Fintype ι]
    (w z : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hz : ∀ i, 0 ≤ z i)
    (k : ℕ) (hk : 0 < k) :
    (∑ i, w i * z i)^k ≤ (∑ i, w i)^(k-1) * ∑ i, w i * (z i)^k := by
  classical
  let A := ∑ i, w i
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => hw i)
  rcases hA.eq_or_lt with hzA | hpA
  · have hw0 : ∀ i, w i = 0 := by
      intro i
      have hi : w i ≤ A := Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ i)
      linarith [hw i]
    simp [hw0, hk.ne']
  · have hs : ∑ i, w i / A = 1 := by
      rw [← Finset.sum_div]
      exact div_self hpA.ne'
    have hj := (convexOn_pow k).map_sum_le (t := Finset.univ)
      (w := fun i => w i / A) (p := z)
      (fun i _ => div_nonneg (hw i) hpA.le) hs (fun i _ => hz i)
    simp only [smul_eq_mul] at hj
    have he (f : ι → ℝ) : ∑ i, w i / A * f i = (∑ i, w i * f i) / A := by
      simp only [div_mul_eq_mul_div, Finset.sum_div]
    rw [he z, he (fun i => z i ^ k), div_pow] at hj
    have hj' := (div_le_div_iff₀ (pow_pos hpA k) hpA).mp hj
    have hkA : A^k = A^(k-1) * A := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hkA] at hj'
    exact (mul_le_mul_iff_left₀ hpA).mp (by nlinarith [hj'])

theorem observationScore_sign (b : Bool) (u : ℝ) :
    observationTranslationScore (boolSign b * u) =
      boolSign b * observationTranslationScore u := by
  cases b <;> simp [boolSign, observationTranslationScore_odd]

theorem observationScorePi_signed_moment {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ε : ι → Bool) (k : ℕ) :
    (∫ u : ι → ℝ, (∑ i, boolSign (ε i) * (a i * observationTranslationScore (u i)))^(2*k)
      ∂Measure.pi (fun _ : ι => observationNoiseLaw)) =
      ∫ u : ι → ℝ, (∑ i, a i * observationTranslationScore (u i))^(2*k)
        ∂Measure.pi (fun _ : ι => observationNoiseLaw) := by
  classical
  have hm : Measurable (fun u : ι → ℝ =>
      (∑ i, a i * observationTranslationScore (u i))^(2*k)) := by
    apply Measurable.pow_const
    exact Finset.measurable_sum _ (fun i _ => measurable_const.mul
      (observationTranslationScore_measurable.comp (measurable_pi_apply i)))
  have hp := observationNoisePi_sign_preserving ε
  have h := integral_map (μ := Measure.pi (fun _ : ι => observationNoiseLaw))
    hp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hp.map_eq] at h
  simpa only [observationScore_sign, mul_left_comm (a _) (boolSign _)] using h.symm

theorem integral_signAverage {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (f : (ι → Bool) → Ω → ℝ)
    (hf : ∀ ε, Integrable (f ε) μ) :
    (∫ u, signAverage (fun ε => f ε u) ∂μ) =
      signAverage (fun ε => ∫ u, f ε u ∂μ) := by
  classical
  unfold signAverage
  rw [integral_const_mul, integral_finsetSum _ (fun ε _ => hf ε)]

theorem observationScorePi_moment_le {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (k : ℕ) (hk : 0 < k) :
    (∫ u : ι → ℝ, |∑ i, a i * observationTranslationScore (u i)|^(2*k)
      ∂Measure.pi (fun _ : ι => observationNoiseLaw)) ≤
      2 * (2048 * Real.exp 1 * (max 1 (2*observationNoiseNormalizer))^2 * (k:ℝ)^5 *
        (∑ i, (a i)^2))^k := by
  classical
  let μ := Measure.pi (fun _ : ι => observationNoiseLaw)
  let A : ℝ := ∑ i, (a i)^2
  let B : ℝ := max 1 (2*observationNoiseNormalizer)
  let K : ℝ := 2 * (2*(k:ℝ)*Real.exp 1)^k
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hq : 2*k ≠ 0 := by omega
  have heven (x : ℝ) : |x|^(2*k) = x^(2*k) := by
    rw [pow_mul, sq_abs, ← pow_mul]
  have hi (ε : ι → Bool) : Integrable (fun u : ι → ℝ =>
      (∑ i, boolSign (ε i) * (a i * observationTranslationScore (u i)))^(2*k)) μ := by
    have hh := observationScorePi_sum_pow_integrable (fun i => boolSign (ε i) * a i)
      (2*k) hq
    simp only [heven, mul_assoc] at hh
    exact hh
  have havgI : Integrable (fun u : ι → ℝ => signAverage
      (fun ε => (∑ i, boolSign (ε i) * (a i * observationTranslationScore (u i)))^(2*k))) μ := by
    exact (integrable_finsetSum _ (fun ε _ => hi ε)).const_mul _
  have hexpI (i : ι) : Integrable (fun u : ι → ℝ =>
      (a i)^2 * |observationTranslationScore (u i)|^(2*k)) μ := by
    exact (((measurePreserving_eval (fun _ : ι => observationNoiseLaw) i).integrable_comp
      (observationScore_pow_integrable (2*k)).aestronglyMeasurable).mpr
        (observationScore_pow_integrable (2*k))).const_mul _
  have hrhsI : Integrable (fun u : ι → ℝ =>
      K * A^(k-1) * (∑ i, (a i)^2 * |observationTranslationScore (u i)|^(2*k))) μ :=
    (integrable_finsetSum _ (fun i _ => hexpI i)).const_mul _
  have hpoint (u : ι → ℝ) : signAverage
      (fun ε => (∑ i, boolSign (ε i) * (a i * observationTranslationScore (u i)))^(2*k)) ≤
      K * A^(k-1) * (∑ i, (a i)^2 * |observationTranslationScore (u i)|^(2*k)) := by
    have hj := weighted_sum_pow_le (fun i => (a i)^2)
      (fun i => (observationTranslationScore (u i))^2) (fun i => sq_nonneg _)
      (fun i => sq_nonneg _) k hk
    simp only [← pow_mul] at hj
    simp only [heven]
    have hkh := signAverage_sum_even_pow
      (fun i => a i * observationTranslationScore (u i)) k hk
    simp only [mul_pow] at hkh
    exact hkh.trans (by simpa only [K, A, mul_pow, mul_assoc] using mul_le_mul_of_nonneg_left hj hK)
  have hint := integral_mono havgI hrhsI hpoint
  rw [integral_signAverage μ _ hi] at hint
  dsimp [μ] at hint
  simp_rw [observationScorePi_signed_moment] at hint
  rw [signAverage_const, integral_const_mul, integral_finsetSum _ (fun i _ => hexpI i)] at hint
  have hcoord (i : ι) : (∫ u : ι → ℝ, (a i)^2 * |observationTranslationScore (u i)|^(2*k) ∂μ) =
      (a i)^2 * (∫ v : ℝ, |observationTranslationScore v|^(2*k) ∂observationNoiseLaw) := by
    rw [integral_const_mul]
    congr 1
    exact integral_comp_eval (μ := fun _ : ι => observationNoiseLaw) (i := i)
      (observationScore_pow_integrable (2*k)).aestronglyMeasurable
  simp_rw [hcoord] at hint
  rw [← Finset.sum_mul] at hint
  have hkA : A^(k-1) * A = A^k := by
    rw [← pow_succ]
    congr 1
    omega
  have hbound := observationScore_moment_le_pow (2*k) (by omega)
  have hbound' := mul_le_mul_of_nonneg_left hbound (mul_nonneg hK (pow_nonneg hA k))
  have hmoment : (∫ u : ι → ℝ, |∑ i, a i * observationTranslationScore (u i)|^(2*k) ∂μ) ≤
      K * A^k * (8 * B * (2*(k:ℝ))^2)^(2*k) := by
    simp only [heven]
    apply le_trans hint
    simpa only [A, B, Nat.cast_mul, Nat.cast_ofNat, mul_assoc, ← hkA] using hbound'
  refine hmoment.trans_eq ?_
  dsimp [K]
  rw [show (8 * B * (2*(k:ℝ))^2)^(2*k) = ((8 * B * (2*(k:ℝ))^2)^2)^k by rw [pow_mul]]
  rw [mul_assoc, ← mul_pow, mul_assoc, ← mul_pow]
  congr 2
  dsimp [A, B]
  ring

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ObservationProductDensity
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
open scoped ENNReal Convolution
open scoped BigOperators

theorem setIntegral_abs_pow_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (s : Set Ω)
    (hp : 0 < μ.real s) (hf : Integrable f μ)
    (q : ℕ) (hq : 0 < q) (hfq : Integrable (fun x => |f x|^q) μ) :
    (∫ x in s, |f x| ∂μ)^q ≤ (μ.real s)^(q-1) * (∫ x, |f x|^q ∂μ) := by
  have h0 : μ s ≠ 0 := by
    intro h
    simp [Measure.real, h] at hp
  have hj := (convexOn_pow q).map_set_average_le
    (continuous_id.pow q).continuousOn isClosed_Ici h0 (measure_ne_top μ s)
    (Filter.Eventually.of_forall (fun x => abs_nonneg (f x)))
    hf.abs.integrableOn hfq.integrableOn
  simp only [average_eq, Measure.real, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, smul_eq_mul, ← div_eq_inv_mul, div_pow] at hj
  change (∫ x in s, |f x| ∂μ)^q / (μ.real s)^q ≤
    (∫ x in s, |f x|^q ∂μ) / μ.real s at hj
  have hj' := (div_le_div_iff₀ (pow_pos hp q) hp).mp hj
  have hpow : (μ.real s)^q = (μ.real s)^(q-1) * μ.real s := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hpow] at hj'
  have hj'' : (∫ x in s, |f x| ∂μ)^q ≤
      (μ.real s)^(q-1) * (∫ x in s, |f x|^q ∂μ) :=
    (mul_le_mul_iff_left₀ hp).mp (by nlinarith [hj'])
  exact hj''.trans (mul_le_mul_of_nonneg_left
    (integral_mono_measure μ.restrict_le_self
      (Filter.Eventually.of_forall fun x => pow_nonneg (abs_nonneg (f x)) q) hfq)
    (pow_nonneg hp.le (q-1)))

theorem square_le_log_fifth_of_moments {x p D : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) (hD : 0 ≤ D)
    (hx : ∀ k : ℕ, 0 < k → x^(2*k) ≤ p^(2*k-1) * (2*(D*(k:ℝ)^5)^k)) :
    x^2 ≤ 32 * Real.exp 2 * D * p^2 * (1-Real.log p)^5 := by
  let L : ℝ := 1-Real.log p
  have hlog : Real.log p ≤ 0 := Real.log_nonpos hp.le hp1
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  let k : ℕ := ⌈L⌉₊
  have hkL : L ≤ (k:ℝ) := Nat.le_ceil L
  have hk : 0 < k := Nat.ceil_pos.mpr (lt_of_lt_of_le zero_lt_one hL)
  have hk1 : 1 ≤ (k:ℝ) := le_trans hL hkL
  have hkU : (k:ℝ) ≤ 2*L := by
    have hh := Nat.ceil_lt_add_one hL0
    change (k:ℝ) < L+1 at hh
    linarith
  have h2p : 2 ≤ p * (Real.exp 2)^k := by
    calc
      2 ≤ Real.exp 1 := Real.exp_one_gt_two.le
      _ ≤ Real.exp (Real.log p + (k:ℝ)*2) := by
        apply Real.exp_le_exp.mpr
        dsimp [L] at hkL
        linarith
      _ = p * (Real.exp 2)^k := by rw [Real.exp_add, Real.exp_log hp, Real.exp_nat_mul]
  have hxp : (x^2)^k ≤ (D * Real.exp 2 * (k:ℝ)^5 * p^2)^k := by
    calc
      (x^2)^k = x^(2*k) := by rw [pow_mul]
      _ ≤ p^(2*k-1) * (2*(D*(k:ℝ)^5)^k) := hx k hk
      _ ≤ p^(2*k-1) * ((p * (Real.exp 2)^k)*(D*(k:ℝ)^5)^k) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right h2p (by positivity)) (by positivity)
      _ = (D * Real.exp 2 * (k:ℝ)^5 * p^2)^k := by
        have he : p^(2*k-1)*p = p^(2*k) := by
          rw [← pow_succ]
          congr 1
          omega
        calc
          p^(2*k-1) * ((p * (Real.exp 2)^k)*(D*(k:ℝ)^5)^k) =
              (p^(2*k-1)*p) * ((Real.exp 2)^k*(D*(k:ℝ)^5)^k) := by ring
          _ = (p^2)^k * ((Real.exp 2)^k*(D*(k:ℝ)^5)^k) := by rw [he, pow_mul]
          _ = (D * Real.exp 2 * (k:ℝ)^5 * p^2)^k := by simp only [mul_pow]; ring
  have hx2 : x^2 ≤ D * Real.exp 2 * (k:ℝ)^5 * p^2 :=
    (pow_le_pow_iff_left₀ (sq_nonneg x) (by positivity) hk.ne').mp hxp
  calc
    x^2 ≤ D * Real.exp 2 * (k:ℝ)^5 * p^2 := hx2
    _ ≤ D * Real.exp 2 * (2*L)^5 * p^2 := by gcongr
    _ = 32 * Real.exp 2 * D * p^2 * (1-Real.log p)^5 := by dsimp [L]; ring

theorem observationScorePi_event_bound {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (s : Set (ι → ℝ))
    (hp : 0 < (Measure.pi (fun _ : ι => observationNoiseLaw)).real s) :
    (∫ u in s, |∑ i, a i * observationTranslationScore (u i)|
      ∂Measure.pi (fun _ : ι => observationNoiseLaw))^2 ≤
      (32 * Real.exp 2 * (2048 * Real.exp 1 * (max 1 (2*observationNoiseNormalizer))^2)) *
        (∑ i, (a i)^2) * ((Measure.pi (fun _ : ι => observationNoiseLaw)).real s)^2 *
        (1-Real.log ((Measure.pi (fun _ : ι => observationNoiseLaw)).real s))^5 := by
  classical
  let μ := Measure.pi (fun _ : ι => observationNoiseLaw)
  let f := fun u : ι → ℝ => ∑ i, a i * observationTranslationScore (u i)
  let D := 2048 * Real.exp 1 * (max 1 (2*observationNoiseNormalizer))^2 *
    (∑ i, (a i)^2)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hf : Integrable f μ := (observationScorePi_sum_memLp a 1 (by omega)).integrable (by norm_num)
  have hh := square_le_log_fifth_of_moments hp measureReal_le_one hD
    (x := ∫ u in s, |f u| ∂μ) (fun k hk => by
      have hi := observationScorePi_sum_pow_integrable a (2*k) (by omega)
      have hj := setIntegral_abs_pow_le μ f s hp hf (2*k) (by omega) hi
      apply hj.trans
      have hb := mul_le_mul_of_nonneg_left (observationScorePi_moment_le a k hk)
        (pow_nonneg hp.le (2*k-1))
      convert hb using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [D]
      congr 3
      ring)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [D]
  ring

open scoped Convolution

theorem observationProductDensity_nonneg {ι : Type*} [Fintype ι] (u : ι → ℝ) :
    0 ≤ observationProductDensity u :=
  Finset.prod_nonneg (fun _i _ => observationNoiseDensity_nonneg _)

theorem observationProductDensity_contDiff {ι : Type*} [Fintype ι] :
    ContDiff ℝ ∞ (@observationProductDensity ι _) := by
  unfold observationProductDensity
  have h := observationNoiseDensity_contDiff
  fun_prop

theorem observationProductDensity_compact {ι : Type*} [Fintype ι] :
    HasCompactSupport (@observationProductDensity ι _) := by
  classical
  apply HasCompactSupport.intro
    (isCompact_pi_infinite (fun _ : ι => (isCompact_Icc : IsCompact (Set.Icc (-1:ℝ) 1))))
  intro u hu
  simp only [Set.mem_ofPred_eq, not_forall] at hu
  obtain ⟨i, hi⟩ := hu
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [observationNoiseDensity_formula, ite_eq_right, mul_zero]
  intro hh
  exact hi ⟨(abs_lt.mp hh).1.le, (abs_lt.mp hh).2.le⟩

theorem observationProductDensity_integrable {ι : Type*} [Fintype ι] :
    Integrable (@observationProductDensity ι _) :=
  Integrable.fintype_prod (fun _ => observationNoiseDensity_integrable)

theorem observationProductDensity_even {ι : Type*} [Fintype ι] (u : ι → ℝ) :
    observationProductDensity (-u) = observationProductDensity u := by
  simp [observationProductDensity, observationNoiseDensity_even]

theorem observationNoiseLaw_pi_density {ι : Type*} [Fintype ι] :
    Measure.pi (fun _ : ι => observationNoiseLaw) =
      volume.withDensity (fun u : ι → ℝ => ENNReal.ofReal (observationProductDensity u)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal observationProductDensity_integrable.integrableOn
      (Filter.Eventually.of_forall observationProductDensity_nonneg)]
  change ENNReal.ofReal (∫ u : ι → ℝ in Set.univ.pi s,
    ∏ i, observationNoiseDensity (u i) ∂Measure.pi (fun _ => volume)) = _
  rw [Measure.restrict_pi_pi, integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg]
  · apply Finset.prod_congr rfl
    intro i _
    rw [observationNoiseLaw, withDensity_apply _ (hs i),
      ← ofReal_integral_eq_lintegral_ofReal observationNoiseDensity_integrable.integrableOn
        (Filter.Eventually.of_forall observationNoiseDensity_nonneg)]
  · intro i _
    exact integral_nonneg observationNoiseDensity_nonneg

theorem observationNoiseLaw_pi_integral {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) :
    (∫ u, f u ∂Measure.pi (fun _ : ι => observationNoiseLaw)) =
      ∫ u, observationProductDensity u * f u := by
  rw [observationNoiseLaw_pi_density, integral_withDensity_eq_integral_toReal_smul]
  · simp only [ENNReal.toReal_ofReal (observationProductDensity_nonneg _), smul_eq_mul]
  · exact observationProductDensity_contDiff.continuous.measurable.ennreal_ofReal
  · exact Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)

theorem observationProductDensity_fderiv {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) :
    fderiv ℝ observationProductDensity u v =
      -(∑ i, v i * observationTranslationScore (u i)) * observationProductDensity u := by
  classical
  have hd (i : ι) : HasFDerivAt (fun w : ι → ℝ => observationNoiseDensity (w i))
      ((-observationTranslationScore (u i) * observationNoiseDensity (u i)) •
        (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) u :=
    (observationNoiseDensity_hasDerivAt (u i)).comp_hasFDerivAt
      (f := fun w : ι → ℝ => w i) u (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt
  unfold observationProductDensity
  rw [(HasFDerivAt.finsetProd (fun i (_ : i ∈ Finset.univ) => hd i)).fderiv]
  simp only [sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [← Finset.sum_neg_distrib, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have he := Finset.mul_prod_erase Finset.univ (fun j => observationNoiseDensity (u j)) hi
  change (∏ j ∈ Finset.univ.erase i, observationNoiseDensity (u j)) *
      ((-observationTranslationScore (u i) * observationNoiseDensity (u i)) * v i) =
    -(v i * observationTranslationScore (u i)) * (∏ j, observationNoiseDensity (u j))
  rw [← he]
  ring

theorem observationEventLikelihood_contDiff {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : MeasurableSet s) :
    ContDiff ℝ ∞ (observationEventLikelihood s) :=
  observationProductDensity_compact.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    ((locallyIntegrable_const 1).indicator hs) observationProductDensity_contDiff

theorem observationEventLikelihood_integral {ι : Type*} [Fintype ι]
    (s : Set (ι → ℝ)) (z : ι → ℝ) :
    observationEventLikelihood s z =
      ∫ u, s.indicator (fun _ => (1:ℝ)) (z+u)
        ∂Measure.pi (fun _ : ι => observationNoiseLaw) := by
  rw [observationEventLikelihood, convolution_def, observationNoiseLaw_pi_integral,
    ← integral_add_left_eq_self (fun y : ι → ℝ =>
      (ContinuousLinearMap.mul ℝ ℝ) (s.indicator (fun _ => (1:ℝ)) y)
        (observationProductDensity (z-y))) z]
  apply integral_congr_ae
  filter_upwards with u
  simp only [ContinuousLinearMap.mul_apply', show z-(z+u) = -u by abel,
    observationProductDensity_even]
  ring

theorem observationEventLikelihood_probability {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : MeasurableSet s) (z : ι → ℝ) :
    observationEventLikelihood s z =
      (Measure.pi (fun _ : ι => observationNoiseLaw)).real ((fun u => z+u) ⁻¹' s) := by
  rw [observationEventLikelihood_integral]
  have he : (fun u => s.indicator (fun _ => (1:ℝ)) (z+u)) =
      ((fun u => z+u) ⁻¹' s).indicator (fun _ => (1:ℝ)) := by
    ext u
    exact (Set.indicator_comp_right (fun u : ι → ℝ => z+u)).symm
  rw [he]
  have ht : MeasurableSet ((fun u : ι → ℝ => z+u) ⁻¹' s) := hs.preimage (by fun_prop)
  rw [integral_indicator ht, setIntegral_const, smul_eq_mul, mul_one]

theorem observationEventLikelihood_fderiv {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : MeasurableSet s) (z v : ι → ℝ) :
    fderiv ℝ (observationEventLikelihood s) z v =
      ∫ u in ((fun u => z+u) ⁻¹' s), ∑ i, v i * observationTranslationScore (u i)
        ∂Measure.pi (fun _ : ι => observationNoiseLaw) := by
  have hf := (locallyIntegrable_const (1:ℝ) (μ := (volume : Measure (ι → ℝ)))).indicator hs
  have hg : ContDiff ℝ 1 (@observationProductDensity ι _) :=
    observationProductDensity_contDiff.of_le (by norm_num)
  have hd := observationProductDensity_compact.hasFDerivAt_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) hf hg z
  change fderiv ℝ (s.indicator (fun _ => (1:ℝ)) ⋆[ContinuousLinearMap.mul ℝ ℝ]
    observationProductDensity) z v = _
  rw [hd.fderiv, convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hf
    (observationProductDensity_compact.fderiv ℝ) (hg.continuous_fderiv one_ne_zero),
    convolution_def]
  have ht : MeasurableSet ((fun u : ι → ℝ => z+u) ⁻¹' s) := hs.preimage (by fun_prop)
  rw [← integral_indicator ht, observationNoiseLaw_pi_integral,
    ← integral_add_left_eq_self (fun y : ι → ℝ =>
      (ContinuousLinearMap.mul ℝ ℝ) (s.indicator (fun _ => (1:ℝ)) y)
        (fderiv ℝ observationProductDensity (z-y) v)) z]
  apply integral_congr_ae
  filter_upwards with u
  rw [observationProductDensity_fderiv]
  simp only [show z-(z+u) = -u by abel, ContinuousLinearMap.mul_apply',
    observationProductDensity_even, Pi.neg_apply, observationTranslationScore_odd,
    mul_neg, Finset.sum_neg_distrib, neg_neg]
  by_cases hu : z+u ∈ s
  · simp [hu, mul_comm]
  · simp [hu]

theorem observationEventLikelihood_nonneg {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : MeasurableSet s) (z : ι → ℝ) :
    0 ≤ observationEventLikelihood s z := by
  rw [observationEventLikelihood_probability hs]
  exact measureReal_nonneg

theorem observationEventLikelihood_le_one {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : MeasurableSet s) (z : ι → ℝ) :
    observationEventLikelihood s z ≤ 1 := by
  rw [observationEventLikelihood_probability hs]
  exact measureReal_le_one

theorem observationScoreConstant_pos : 0 < observationScoreConstant := by
  unfold observationScoreConstant
  have : 0 < max 1 (2*observationNoiseNormalizer) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  positivity

theorem observationEventLikelihood_derivative_bound {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : MeasurableSet s) (z v : ι → ℝ) :
    (fderiv ℝ (observationEventLikelihood s) z v)^2 ≤
      observationScoreConstant * (∑ i, (v i)^2) * (observationEventLikelihood s z)^2 *
        (1-Real.log (observationEventLikelihood s z))^5 := by
  let μ := Measure.pi (fun _ : ι => observationNoiseLaw)
  let t := (fun u : ι → ℝ => z+u) ⁻¹' s
  rw [observationEventLikelihood_fderiv hs, observationEventLikelihood_probability hs]
  change (∫ u in t, ∑ i, v i * observationTranslationScore (u i) ∂μ)^2 ≤
    observationScoreConstant * (∑ i, (v i)^2) * (μ.real t)^2 * (1-Real.log (μ.real t))^5
  rcases (measureReal_nonneg : 0 ≤ μ.real t).eq_or_lt with hp | hp
  · have hzero : μ t = 0 := (ENNReal.toReal_eq_zero_iff _).mp hp.symm |>.resolve_right (measure_ne_top μ t)
    simp [Measure.restrict_eq_zero.mpr hzero, hp.symm]
  · have hh := observationScorePi_event_bound v t hp
    apply le_trans _ hh
    have ha := abs_integral_le_integral_abs (f := fun u : ι → ℝ =>
      ∑ i, v i * observationTranslationScore (u i)) (μ := μ.restrict t)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) ha 2

theorem likelihood_log_fifth_majorant {u p : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hp : 0 < p) (hp1 : p ≤ 1) :
    u * (1-Real.log u)^5 ≤
      (u + 120 * Real.exp 1 * p) * (1-Real.log p)^5 := by
  have hL : 1 ≤ 1-Real.log p := by have := Real.log_nonpos hp.le hp1; linarith
  have hL0 : 0 ≤ 1-Real.log p := by linarith
  rcases hu.eq_or_lt with rfl | hu
  · simp only [zero_mul, zero_add]
    positivity
  by_cases hup : u ≤ p
  · let t := Real.log p - Real.log u
    have ht : 0 ≤ t := sub_nonneg.mpr (Real.log_le_log hu hup)
    have hpow : (1-Real.log u)^5 ≤ ((1-Real.log p)*(1+t))^5 := by
      apply pow_le_pow_left₀ (by have := Real.log_nonpos hu.le hu1; linarith)
      have he : 1-Real.log u = (1-Real.log p)+t := by dsimp [t]; ring
      rw [he]
      nlinarith
    have hex := pow_mul_exp_neg_le_factorial 5 (add_nonneg zero_le_one ht)
    have hex' : (1+t)^5 * Real.exp (-t) ≤ 120 * Real.exp 1 := by
      have hh := mul_le_mul_of_nonneg_right hex (Real.exp_pos 1).le
      rw [mul_assoc, ← Real.exp_add] at hh
      convert hh using 1 <;> first | rfl | norm_num
    have he : u = p * Real.exp (-t) := by
      dsimp [t]
      rw [neg_sub, Real.exp_sub, Real.exp_log hu, Real.exp_log hp]
      field_simp
    calc
      u * (1-Real.log u)^5 ≤ u * ((1-Real.log p)*(1+t))^5 :=
        mul_le_mul_of_nonneg_left hpow hu.le
      _ = p * (1-Real.log p)^5 * ((1+t)^5 * Real.exp (-t)) := by rw [he, mul_pow]; ring
      _ ≤ p * (1-Real.log p)^5 * (120 * Real.exp 1) :=
        mul_le_mul_of_nonneg_left hex' (by positivity)
      _ ≤ (u + 120 * Real.exp 1 * p) * (1-Real.log p)^5 := by
        nlinarith [mul_nonneg hu.le (pow_nonneg hL0 5)]
  · have hpu : p ≤ u := (lt_of_not_ge hup).le
    have hl : 1-Real.log u ≤ 1-Real.log p := sub_le_sub_left (Real.log_le_log hp hpu) 1
    have h0 : 0 ≤ 1-Real.log u := by have := Real.log_nonpos hu.le hu1; linarith
    calc
      u * (1-Real.log u)^5 ≤ u * (1-Real.log p)^5 := by gcongr
      _ ≤ (u + 120 * Real.exp 1 * p) * (1-Real.log p)^5 := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hL0 5)
        exact le_add_of_nonneg_right (by positivity)

theorem arrayEventLikelihood_contDiff {H : Type*} [Fintype H] {n : ℕ}
    (ℓ : H → ℝ) {s : Set ((H × (Fin n × Fin 3)) → ℝ)} (hs : MeasurableSet s) :
    ContDiff ℝ ∞ (arrayEventLikelihood ℓ s) :=
  (observationEventLikelihood_contDiff (hs.preimage (by
    unfold observationArrayRescale; fun_prop))).comp (observationArrayCenter ℓ).contDiff

theorem arrayEventLikelihood_nonneg {H : Type*} [Fintype H] {n : ℕ}
    (ℓ : H → ℝ) {s : Set ((H × (Fin n × Fin 3)) → ℝ)} (hs : MeasurableSet s)
    (x : Configuration n) : 0 ≤ arrayEventLikelihood ℓ s x :=
  observationEventLikelihood_nonneg (hs.preimage (by unfold observationArrayRescale; fun_prop)) _

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ObservationWidthSquareSum
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
open scoped ENNReal Convolution
open scoped BigOperators
open scoped Convolution

theorem arrayEventLikelihood_le_one {H : Type*} [Fintype H] {n : ℕ}
    (ℓ : H → ℝ) {s : Set ((H × (Fin n × Fin 3)) → ℝ)} (hs : MeasurableSet s)
    (x : Configuration n) : arrayEventLikelihood ℓ s x ≤ 1 :=
  observationEventLikelihood_le_one (hs.preimage (by unfold observationArrayRescale; fun_prop)) _

theorem arrayEventLikelihood_integral {H : Type*} [Fintype H] {n : ℕ}
    (ℓ : H → ℝ) (hℓ : ∀ h, ℓ h ≠ 0)
    (s : Set ((H × (Fin n × Fin 3)) → ℝ)) (x : Configuration n) :
    arrayEventLikelihood ℓ s x =
      ∫ u, s.indicator (fun _ => (1:ℝ)) (fun hia => x hia.2.1 hia.2.2 + ℓ hia.1 * u hia)
        ∂Measure.pi (fun _ : H × (Fin n × Fin 3) => observationNoiseLaw) := by
  rw [arrayEventLikelihood, observationEventLikelihood_integral]
  apply integral_congr_ae
  filter_upwards with u
  have he : observationArrayRescale ℓ (observationArrayCenter ℓ x + u) =
      (fun hia => x hia.2.1 hia.2.2 + ℓ hia.1 * u hia) := by
    ext hia
    simp [observationArrayRescale, observationArrayCenter, mul_add, hℓ]
  change (observationArrayRescale ℓ ⁻¹' s).indicator
    ((fun _ => (1:ℝ)) ∘ observationArrayRescale ℓ) (observationArrayCenter ℓ x + u) = _
  rw [Set.indicator_comp_right, he]

theorem observationWidthSquareSum_nonneg {H : Type*} [Fintype H] (ℓ : H → ℝ) :
    0 ≤ observationWidthSquareSum ℓ := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem arrayEventLikelihood_direction_bound {H : Type*} [Fintype H] {n : ℕ}
    (ℓ : H → ℝ) {s : Set ((H × (Fin n × Fin 3)) → ℝ)} (hs : MeasurableSet s)
    (x v : Configuration n) :
    (fderiv ℝ (arrayEventLikelihood ℓ s) x v)^2 ≤
      observationScoreConstant * observationWidthSquareSum ℓ * (∑ i, ∑ a, (v i a)^2) *
        (arrayEventLikelihood ℓ s x)^2 * (1-Real.log (arrayEventLikelihood ℓ s x))^5 := by
  have ht : MeasurableSet (observationArrayRescale ℓ ⁻¹' s) := hs.preimage (by
    unfold observationArrayRescale; fun_prop)
  have hd := (observationEventLikelihood_contDiff ht).differentiable (by simp)
  have he : fderiv ℝ (arrayEventLikelihood ℓ s) x v =
      fderiv ℝ (observationEventLikelihood (observationArrayRescale ℓ ⁻¹' s))
        (observationArrayCenter ℓ x) (observationArrayCenter ℓ v) := by
    exact congrArg (fun D : Configuration n →L[ℝ] ℝ => D v)
      ((hd _).hasFDerivAt.comp x (observationArrayCenter ℓ).hasFDerivAt).fderiv
  rw [he]
  have hh := observationEventLikelihood_derivative_bound ht (observationArrayCenter ℓ x)
    (observationArrayCenter ℓ v)
  have hsum : (∑ hia : H × (Fin n × Fin 3), (observationArrayCenter ℓ v hia)^2) =
      observationWidthSquareSum ℓ * (∑ i, ∑ a, (v i a)^2) := by
    simp only [observationArrayCenter, ContinuousLinearMap.pi_apply, smul_apply,
      smul_eq_mul, coordinateLinear_apply, mul_pow, Fintype.sum_prod_type,
      ← Finset.mul_sum, ← Finset.sum_mul, observationWidthSquareSum]
  simpa only [hsum, arrayEventLikelihood, mul_assoc] using hh

theorem configuration_coordinate_expansion {n : ℕ} (v : Configuration n) :
    v = ∑ i, ∑ a, (v i a) • coordinateDirection i a := by
  classical
  ext i a
  simp [coordinateDirection, Pi.single_apply]

theorem arrayEventLikelihood_gradient_bound {H : Type*} [Fintype H] {n : ℕ}
    (ℓ : H → ℝ) {s : Set ((H × (Fin n × Fin 3)) → ℝ)} (hs : MeasurableSet s)
    (x : Configuration n) :
    (∑ i, ∑ a, (fderiv ℝ (arrayEventLikelihood ℓ s) x (coordinateDirection i a))^2) ≤
      observationScoreConstant * observationWidthSquareSum ℓ *
        (arrayEventLikelihood ℓ s x)^2 * (1-Real.log (arrayEventLikelihood ℓ s x))^5 := by
  let d : Fin n → Fin 3 → ℝ := fun i a =>
    fderiv ℝ (arrayEventLikelihood ℓ s) x (coordinateDirection i a)
  let v : Configuration n := fun i => (EuclideanSpace.equiv (Fin 3) ℝ).symm (d i)
  let A : ℝ := ∑ i, ∑ a, (d i a)^2
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun a _ => sq_nonneg _))
  have hv (i : Fin n) (a : Fin 3) : v i a = d i a := rfl
  have he : fderiv ℝ (arrayEventLikelihood ℓ s) x v = A := by
    conv_lhs => rw [configuration_coordinate_expansion v]
    simp only [map_sum, map_smul, smul_eq_mul, hv, d, A, pow_two]
  have hh := arrayEventLikelihood_direction_bound ℓ hs x v
  simp only [he, hv] at hh
  change A^2 ≤ observationScoreConstant * observationWidthSquareSum ℓ * A *
    (arrayEventLikelihood ℓ s x)^2 * (1-Real.log (arrayEventLikelihood ℓ s x))^5 at hh
  change A ≤ _
  rcases hA.eq_or_lt with hAz | hAz
  · rw [← hAz]
    have hl := Real.log_nonpos (arrayEventLikelihood_nonneg ℓ hs x) (arrayEventLikelihood_le_one ℓ hs x)
    exact mul_nonneg (mul_nonneg (mul_nonneg observationScoreConstant_pos.le
      (observationWidthSquareSum_nonneg ℓ)) (sq_nonneg _)) (pow_nonneg (by linarith) 5)
  · exact (mul_le_mul_iff_left₀ hAz).mp (by nlinarith only [hh])

theorem arrayEventLikelihood_symmetric {H : Type*} [Fintype H] {n : ℕ}
    (ℓ : H → ℝ) (hℓ : ∀ h, ℓ h ≠ 0)
    {s : Set ((H × (Fin n × Fin 3)) → ℝ)}
    (hsym : ∀ (p : Equiv.Perm (Fin n)) y, permuteObservationArray p y ∈ s ↔ y ∈ s)
    (p : Equiv.Perm (Fin n)) (x : Configuration n) :
    arrayEventLikelihood ℓ s (x ∘ p) = arrayEventLikelihood ℓ s x := by
  rw [arrayEventLikelihood_integral ℓ hℓ, arrayEventLikelihood_integral ℓ hℓ]
  let e : Equiv.Perm (H × (Fin n × Fin 3)) :=
    Equiv.prodCongr (Equiv.refl H) (Equiv.prodCongr p (Equiv.refl (Fin 3)))
  let F : ((H × (Fin n × Fin 3)) → ℝ) → ℝ := fun u =>
    s.indicator (fun _ => (1:ℝ)) (fun hia => (x ∘ p) hia.2.1 hia.2.2 + ℓ hia.1 * u hia)
  have he := (measurePreserving_piCongrLeft
    (fun _ : H × (Fin n × Fin 3) => observationNoiseLaw) e.symm).integral_comp' F
  rw [← he]
  apply integral_congr_ae
  filter_upwards with u
  have hu : (MeasurableEquiv.piCongrLeft (fun _ : H × (Fin n × Fin 3) => ℝ) e.symm) u =
      permuteObservationArray p u := by
    ext hia
    have hh := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ) e.symm u (e hia)
    rw [e.symm_apply_apply] at hh
    exact hh
  rw [hu]
  dsimp only [F]
  have hv : (fun hia => (x ∘ p) hia.2.1 hia.2.2 + ℓ hia.1 * permuteObservationArray p u hia) =
      permuteObservationArray p (fun hia => x hia.2.1 hia.2.2 + ℓ hia.1 * u hia) := rfl
  rw [hv]
  simp only [Set.indicator, hsym]

theorem regularizedEventRoot_derivative {n : ℕ} {F : Configuration n → ℝ}
    (hF : ContDiff ℝ ∞ F) (hF0 : ∀ x, 0 ≤ F x)
    (k : ℕ) (i : Fin n) (a : Fin 3) (x : Configuration n) :
    fderiv ℝ (regularizedEventRoot F k) x (coordinateDirection i a) =
      fderiv ℝ F x (coordinateDirection i a) / (2 * regularizedEventRoot F k x) := by
  have hpos : 0 < 1/((k:ℝ)+1) + F x := add_pos_of_pos_of_nonneg (by positivity) (hF0 x)
  unfold regularizedEventRoot
  rw [fderiv_sqrt ((contDiff_const.add hF).differentiable (by simp)).differentiableAt hpos.ne',
    fderiv_const_add]
  simp only [smul_apply, smul_eq_mul]
  ring

theorem root_gradient_square_bound {n : ℕ} {F : Configuration n → ℝ}
    {K : ℝ} (hK : 0 ≤ K) (hF0 : ∀ x, 0 ≤ F x) (hF1 : ∀ x, F x ≤ 1)
    (hgrad : ∀ x, (∑ i, ∑ a, (fderiv ℝ F x (coordinateDirection i a))^2) ≤
      K * (F x)^2 * (1-Real.log (F x))^5)
    {ε : ℝ} (hε : 0 ≤ ε) (x : Configuration n) :
    (∑ i, ∑ a, (fderiv ℝ F x (coordinateDirection i a) /
      (2 * Real.sqrt (ε + F x)))^2) ≤ K/4 * F x * (1-Real.log (F x))^5 := by
  have hlog : 0 ≤ (1-Real.log (F x))^5 := by
    apply pow_nonneg
    have := Real.log_nonpos (hF0 x) (hF1 x)
    linarith
  rcases (add_nonneg hε (hF0 x)).eq_or_lt with hh | hh
  · rw [← hh, Real.sqrt_zero, mul_zero]
    simp only [div_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]
    exact mul_nonneg (mul_nonneg (div_nonneg hK (by norm_num)) (hF0 x)) hlog
  · simp only [div_pow, mul_pow, Real.sq_sqrt hh.le, ← Finset.sum_div]
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2^2*(ε+F x))).mpr
    have hnonneg := mul_nonneg (mul_nonneg (mul_nonneg hK (hF0 x)) hlog) hε
    nlinarith [hgrad x]

theorem eventRootDerivative_gradient_bound {n : ℕ} {F : Configuration n → ℝ}
    {K : ℝ} (hK : 0 ≤ K) (hF0 : ∀ x, 0 ≤ F x) (hF1 : ∀ x, F x ≤ 1)
    (hgrad : ∀ x, (∑ i, ∑ a, (fderiv ℝ F x (coordinateDirection i a))^2) ≤
      K * (F x)^2 * (1-Real.log (F x))^5) (x : Configuration n) :
    (∑ i, ∑ a, (eventRootDerivative F i a x)^2) ≤
      K/4 * F x * (1-Real.log (F x))^5 := by
  simpa only [zero_add, eventRootDerivative] using
    root_gradient_square_bound hK hF0 hF1 hgrad (ε := 0) le_rfl x

theorem coordinate_square_le_sum {n : ℕ} (D : Fin n → Fin 3 → ℝ)
    (i : Fin n) (a : Fin 3) : (D i a)^2 ≤ ∑ j, ∑ b, (D j b)^2 := by
  apply (Finset.single_le_sum (fun b _ => sq_nonneg (D i b)) (Finset.mem_univ a)).trans
  exact Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun b _ => sq_nonneg (D j b)))
    (Finset.mem_univ i)

theorem regularizedEventRoot_tendsto {n : ℕ} (F : Configuration n → ℝ)
    (x : Configuration n) :
    Tendsto (fun k => regularizedEventRoot F k x) atTop (𝓝 (Real.sqrt (F x))) := by
  have ht : Tendsto (fun k : ℕ => 1/((k:ℝ)+1) + F x) atTop (𝓝 (F x)) := by
    simpa only [zero_add] using tendsto_one_div_add_atTop_nhds_zero_nat.add_const (F x)
  exact Real.continuous_sqrt.continuousAt.tendsto.comp ht

theorem likelihood_log_fifth_nonneg {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ u * (1-Real.log u)^5 := by
  have := Real.log_nonpos hu hu1
  exact mul_nonneg hu (pow_nonneg (by linarith) 5)

theorem likelihood_log_fifth_bounded {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    u * (1-Real.log u)^5 ≤ 1+120*Real.exp 1 := by
  have hh := likelihood_log_fifth_majorant hu hu1 (p := 1) (by norm_num) le_rfl
  simp only [Real.log_one, sub_zero, one_pow, mul_one] at hh
  linarith

theorem likelihood_gradient_zero {n : ℕ} {F : Configuration n → ℝ} {K : ℝ}
    (hgrad : ∀ x, (∑ i, ∑ a, (fderiv ℝ F x (coordinateDirection i a))^2) ≤
      K * (F x)^2 * (1-Real.log (F x))^5)
    {x : Configuration n} (hzero : F x = 0) (i : Fin n) (a : Fin 3) :
    fderiv ℝ F x (coordinateDirection i a) = 0 := by
  have hh := (coordinate_square_le_sum
    (fun i a => fderiv ℝ F x (coordinateDirection i a)) i a).trans (hgrad x)
  rw [hzero] at hh
  nlinarith [sq_nonneg (fderiv ℝ F x (coordinateDirection i a))]

theorem regularizedEventRoot_contDiff {n : ℕ} {F : Configuration n → ℝ}
    (hF : ContDiff ℝ ∞ F) (hF0 : ∀ x, 0 ≤ F x) (k : ℕ) :
    ContDiff ℝ ∞ (regularizedEventRoot F k) :=
  (contDiff_const.add hF).sqrt (fun x =>
    (add_pos_of_pos_of_nonneg (by positivity) (hF0 x)).ne')

theorem regularizedEventRoot_bound {n : ℕ} {F : Configuration n → ℝ}
    (hF1 : ∀ x, F x ≤ 1) (k : ℕ) (x : Configuration n) :
    |regularizedEventRoot F k x| ≤ Real.sqrt 2 := by
  rw [regularizedEventRoot, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply Real.sqrt_le_sqrt
  have hh : 1/((k:ℝ)+1) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  linarith [hF1 x]

theorem regularizedEventRoot_derivative_bound {n : ℕ} {F : Configuration n → ℝ}
    {K : ℝ} (hK : 0 ≤ K) (hF : ContDiff ℝ ∞ F)
    (hF0 : ∀ x, 0 ≤ F x) (hF1 : ∀ x, F x ≤ 1)
    (hgrad : ∀ x, (∑ i, ∑ a, (fderiv ℝ F x (coordinateDirection i a))^2) ≤
      K * (F x)^2 * (1-Real.log (F x))^5)
    (k : ℕ) (i : Fin n) (a : Fin 3) (x : Configuration n) :
    |fderiv ℝ (regularizedEventRoot F k) x (coordinateDirection i a)| ≤
      Real.sqrt (K/4*(1+120*Real.exp 1)) := by
  rw [regularizedEventRoot_derivative hF hF0]
  apply Real.abs_le_sqrt
  apply (coordinate_square_le_sum
    (fun i a => fderiv ℝ F x (coordinateDirection i a) /
      (2*regularizedEventRoot F k x)) i a).trans
  calc
    _ ≤ K/4 * F x * (1-Real.log (F x))^5 :=
      root_gradient_square_bound hK hF0 hF1 hgrad (by positivity) x
    _ ≤ K/4*(1+120*Real.exp 1) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (likelihood_log_fifth_bounded (hF0 x) (hF1 x))
        (div_nonneg hK (by norm_num))

theorem regularizedEventRoot_derivative_tendsto {n : ℕ} {F : Configuration n → ℝ}
    {K : ℝ} (hF : ContDiff ℝ ∞ F) (hF0 : ∀ x, 0 ≤ F x)
    (hgrad : ∀ x, (∑ i, ∑ a, (fderiv ℝ F x (coordinateDirection i a))^2) ≤
      K * (F x)^2 * (1-Real.log (F x))^5)
    (i : Fin n) (a : Fin 3) (x : Configuration n) :
    Tendsto (fun k => fderiv ℝ (regularizedEventRoot F k) x (coordinateDirection i a))
      atTop (𝓝 (eventRootDerivative F i a x)) := by
  simp_rw [regularizedEventRoot_derivative hF hF0]
  unfold eventRootDerivative
  by_cases hz : F x = 0
  · simp_rw [likelihood_gradient_zero hgrad hz i a, zero_div]
    exact tendsto_const_nhds
  · exact tendsto_const_nhds.div (tendsto_const_nhds.mul (regularizedEventRoot_tendsto F x))
      (mul_ne_zero (by norm_num) (Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (hF0 x) (Ne.symm hz))))

theorem eventRootDerivative_measurable {n : ℕ} {F : Configuration n → ℝ}
    (hF : ContDiff ℝ ∞ F) (i : Fin n) (a : Fin 3) :
    Measurable (eventRootDerivative F i a) :=
  (((hF.continuous_fderiv (by simp)).clm_apply continuous_const).measurable).div
    (measurable_const.mul (Real.continuous_sqrt.comp hF.continuous).measurable)

theorem eventRootDerivative_bound {n : ℕ} {F : Configuration n → ℝ}
    {K : ℝ} (hK : 0 ≤ K) (hF0 : ∀ x, 0 ≤ F x) (hF1 : ∀ x, F x ≤ 1)
    (hgrad : ∀ x, (∑ i, ∑ a, (fderiv ℝ F x (coordinateDirection i a))^2) ≤
      K * (F x)^2 * (1-Real.log (F x))^5)
    (i : Fin n) (a : Fin 3) (x : Configuration n) :
    |eventRootDerivative F i a x| ≤ Real.sqrt (K/4*(1+120*Real.exp 1)) := by
  apply Real.abs_le_sqrt
  apply (coordinate_square_le_sum (fun i a => eventRootDerivative F i a x) i a).trans
  exact (eventRootDerivative_gradient_bound hK hF0 hF1 hgrad x).trans (by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (likelihood_log_fifth_bounded (hF0 x) (hF1 x))
      (div_nonneg hK (by norm_num)))

theorem FormDomain.eventRoot {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) {F : Configuration n → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hF : ContDiff ℝ ∞ F) (hF0 : ∀ x, 0 ≤ F x) (hF1 : ∀ x, F x ≤ 1)
    (hsym : ∀ (p : Equiv.Perm (Fin n)) x, F (x ∘ p) = F x)
    (hgrad : ∀ x, (∑ i, ∑ a, (fderiv ℝ F x (coordinateDirection i a))^2) ≤
      K * (F x)^2 * (1-Real.log (F x))^5) :
    FormDomain (multiplyWavefunction (fun x => Real.sqrt (F x)) ψ)
      (explicitMultiplyGradient (fun x => Real.sqrt (F x)) (eventRootDerivative F) ψ g) := by
  apply hd.multiply_limit (θk := regularizedEventRoot F)
    (Real.continuous_sqrt.comp hF.continuous) (fun p x => by dsimp only [Function.comp_apply]; rw [hsym p x])
    (fun i a => (eventRootDerivative_measurable hF i a).aestronglyMeasurable)
    (regularizedEventRoot_contDiff hF hF0)
    ⟨Real.sqrt 2, regularizedEventRoot_bound hF1⟩
    (fun i a => ⟨_, fun k x => regularizedEventRoot_derivative_bound hK hF hF0 hF1 hgrad k i a x⟩)
    (regularizedEventRoot_tendsto F)
    (regularizedEventRoot_derivative_tendsto hF hF0 hgrad)

theorem likelihood_smoothMultiplier {n : ℕ} {F : Configuration n → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hF : ContDiff ℝ ∞ F) (hF0 : ∀ x, 0 ≤ F x) (hF1 : ∀ x, F x ≤ 1)
    (hsym : ∀ (p : Equiv.Perm (Fin n)) x, F (x ∘ p) = F x)
    (hgrad : ∀ x, (∑ i, ∑ a, (fderiv ℝ F x (coordinateDirection i a))^2) ≤
      K * (F x)^2 * (1-Real.log (F x))^5) : SmoothMultiplier F := by
  refine ⟨hF, hsym, ⟨1, fun x => by rw [abs_of_nonneg (hF0 x)]; exact hF1 x⟩, ?_⟩
  intro i a
  refine ⟨Real.sqrt (K*(1+120*Real.exp 1)), fun x => Real.abs_le_sqrt ?_⟩
  apply (coordinate_square_le_sum (fun i a => fderiv ℝ F x (coordinateDirection i a)) i a).trans
  apply (hgrad x).trans
  calc
    K * F x^2 * (1-Real.log (F x))^5 = K * F x * (F x * (1-Real.log (F x))^5) := by ring
    _ ≤ K * 1 * (1+120*Real.exp 1) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hF1 x) hK)
        (likelihood_log_fifth_bounded (hF0 x) (hF1 x))
        (likelihood_log_fifth_nonneg (hF0 x) (hF1 x)) (by positivity)
    _ = _ := by ring

theorem eventRoot_square_derivative {n : ℕ} {F : Configuration n → ℝ} {K : ℝ}
    (hF0 : ∀ x, 0 ≤ F x)
    (hgrad : ∀ x, (∑ i, ∑ a, (fderiv ℝ F x (coordinateDirection i a))^2) ≤
      K * (F x)^2 * (1-Real.log (F x))^5)
    (i : Fin n) (a : Fin 3) (x : Configuration n) :
    fderiv ℝ (fun y => (Real.sqrt (F y))^2) x (coordinateDirection i a) =
      2*Real.sqrt (F x)*eventRootDerivative F i a x := by
  simp_rw [Real.sq_sqrt (hF0 _)]
  unfold eventRootDerivative
  by_cases hz : F x = 0
  · rw [likelihood_gradient_zero hgrad hz i a]; simp
  · field_simp [Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (hF0 x) (Ne.symm hz))]

theorem stateWeighted_integrable {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) {F : Configuration n → ℝ} (hF : Measurable F)
    {C : ℝ} (hFb : ∀ x, |F x| ≤ C) (σ : Spins n) :
    Integrable (fun x => F x * ‖ψ σ x‖^2) :=
  (hd.2.2.1 σ).norm.integrable_sq.bdd_mul hF.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hFb x)

theorem stateWeightedIntegral_le_one {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (hn : normSquared ψ = 1)
    {F : Configuration n → ℝ} (hF : Measurable F)
    (hF0 : ∀ x, 0 ≤ F x) (hF1 : ∀ x, F x ≤ 1) : stateWeightedIntegral ψ F ≤ 1 := by
  rw [← hn]
  apply Finset.sum_le_sum
  intro σ _
  apply integral_mono (stateWeighted_integrable hd hF (C := 1)
    (fun x => by rw [abs_of_nonneg (hF0 x)]; exact hF1 x) σ) (hd.2.2.1 σ).norm.integrable_sq
  intro x
  exact mul_le_of_le_one_left (sq_nonneg _) (hF1 x)

theorem stateWeightedIntegral_log_fifth {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (hn : normSquared ψ = 1)
    {F : Configuration n → ℝ} (hF : Measurable F)
    (hF0 : ∀ x, 0 ≤ F x) (hF1 : ∀ x, F x ≤ 1)
    (hp : 0 < stateWeightedIntegral ψ F) :
    stateWeightedIntegral ψ (fun x => F x*(1-Real.log (F x))^5) ≤
      (1+120*Real.exp 1)*stateWeightedIntegral ψ F*
        (1-Real.log (stateWeightedIntegral ψ F))^5 := by
  let p := stateWeightedIntegral ψ F
  have hp1 : p ≤ 1 := stateWeightedIntegral_le_one hd hn hF hF0 hF1
  have hfi (σ : Spins n) := stateWeighted_integrable hd hF (C := 1)
    (fun x => by rw [abs_of_nonneg (hF0 x)]; exact hF1 x) σ
  have hli (σ : Spins n) := stateWeighted_integrable hd
    (F := fun x => F x*(1-Real.log (F x))^5)
    (hF.mul ((measurable_const.sub hF.log).pow_const 5))
    (C := 1+120*Real.exp 1)
    (fun x => by rw [abs_of_nonneg (likelihood_log_fifth_nonneg (hF0 x) (hF1 x))]
                 exact likelihood_log_fifth_bounded (hF0 x) (hF1 x)) σ
  have hh (σ : Spins n) :
      (∫ x, (F x*(1-Real.log (F x))^5)*‖ψ σ x‖^2) ≤
        ((∫ x, F x*‖ψ σ x‖^2) + 120*Real.exp 1*p*(∫ x, ‖ψ σ x‖^2))*
          (1-Real.log p)^5 := by
    calc
      _ ≤ ∫ x, ((F x+120*Real.exp 1*p)*‖ψ σ x‖^2)*(1-Real.log p)^5 := by
        apply integral_mono (hli σ)
          (((hfi σ).add ((hd.2.2.1 σ).norm.integrable_sq.const_mul (120*Real.exp 1*p))).mul_const ((1-Real.log p)^5) |>.congr
            (Eventually.of_forall fun x => by dsimp only [Pi.add_apply]; ring))
        intro x
        have ht := mul_le_mul_of_nonneg_right
          (likelihood_log_fifth_majorant (hF0 x) (hF1 x) hp hp1) (sq_nonneg ‖ψ σ x‖)
        nlinarith only [ht]
      _ = _ := by
        rw [integral_mul_const]
        congr 1
        simp_rw [add_mul]
        rw [integral_add (hfi σ) ((hd.2.2.1 σ).norm.integrable_sq.const_mul (120*Real.exp 1*p)),
          integral_const_mul]
  have hs := Finset.sum_le_sum (fun σ (_ : σ ∈ (Finset.univ : Finset (Spins n))) => hh σ)
  simp only [← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  change stateWeightedIntegral ψ (fun x => F x*(1-Real.log (F x))^5) ≤
    (p+120*Real.exp 1*p*normSquared ψ)*(1-Real.log p)^5 at hs
  rw [hn] at hs
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [p]
  ring

theorem explicitLocalizationError_eventRoot_le {n : ℕ}
    {ψ : Wavefunction n} {g : Gradient n} (hd : FormDomain ψ g)
    (hn : normSquared ψ = 1) {F : Configuration n → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hF : ContDiff ℝ ∞ F) (hF0 : ∀ x, 0 ≤ F x) (hF1 : ∀ x, F x ≤ 1)
    (hgrad : ∀ x, (∑ i, ∑ a, (fderiv ℝ F x (coordinateDirection i a))^2) ≤
      K * (F x)^2 * (1-Real.log (F x))^5)
    (hp : 0 < stateWeightedIntegral ψ F) :
    explicitLocalizationError ψ (eventRootDerivative F) ≤
      K/8*(1+120*Real.exp 1)*stateWeightedIntegral ψ F*
        (1-Real.log (stateWeightedIntegral ψ F))^5 := by
  have hdi (σ : Spins n) (i : Fin n) (a : Fin 3) :
      Integrable (fun x => (eventRootDerivative F i a x)^2*‖ψ σ x‖^2) := by
    have hl := memLp_bounded_measurable_real_smul (hd.2.2.1 σ)
      (eventRootDerivative_measurable hF i a).aestronglyMeasurable
      ⟨_, eventRootDerivative_bound hK hF0 hF1 hgrad i a⟩
    simpa only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] using hl.norm.integrable_sq
  have hli (σ : Spins n) := stateWeighted_integrable hd
    (F := fun x => F x*(1-Real.log (F x))^5)
    (hF.continuous.measurable.mul ((measurable_const.sub hF.continuous.measurable.log).pow_const 5))
    (C := 1+120*Real.exp 1)
    (fun x => by rw [abs_of_nonneg (likelihood_log_fifth_nonneg (hF0 x) (hF1 x))]
                 exact likelihood_log_fifth_bounded (hF0 x) (hF1 x)) σ
  have hs (σ : Spins n) :
      (∑ i, ∑ a, ∫ x, (eventRootDerivative F i a x)^2*‖ψ σ x‖^2) ≤
        K/4 * ∫ x, (F x*(1-Real.log (F x))^5)*‖ψ σ x‖^2 := by
    calc
      _ = ∫ x, (∑ i, ∑ a, (eventRootDerivative F i a x)^2)*‖ψ σ x‖^2 := by
        simp_rw [Finset.sum_mul]
        rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun a _ => hdi σ i a))]
        apply Finset.sum_congr rfl
        intro i _
        exact (integral_finsetSum _ (fun a _ => hdi σ i a)).symm
      _ ≤ ∫ x, K/4*((F x*(1-Real.log (F x))^5)*‖ψ σ x‖^2) := by
        apply integral_mono
        · simpa only [Finset.sum_mul] using
            integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun a _ => hdi σ i a))
        · exact (hli σ).const_mul _
        · intro x
          have hh := mul_le_mul_of_nonneg_right
            (eventRootDerivative_gradient_bound hK hF0 hF1 hgrad x) (sq_nonneg ‖ψ σ x‖)
          nlinarith only [hh]
      _ = _ := integral_const_mul _ _
  have hh := mul_le_mul_of_nonneg_left (Finset.sum_le_sum
    (fun σ (_ : σ ∈ (Finset.univ : Finset (Spins n))) => hs σ)) (by norm_num : (0:ℝ) ≤ 1/2)
  simp only [← Finset.mul_sum] at hh
  change explicitLocalizationError ψ (eventRootDerivative F) ≤
    (1/2)*(K/4*stateWeightedIntegral ψ (fun x => F x*(1-Real.log (F x))^5)) at hh
  apply hh.trans
  have hlog := mul_le_mul_of_nonneg_left
    (stateWeightedIntegral_log_fifth hd hn hF.continuous.measurable hF0 hF1 hp)
    (div_nonneg hK (by norm_num : (0:ℝ) ≤ 8))
  nlinarith only [hlog]

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_EventTiltWavefunction
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
open scoped ENNReal Convolution
open scoped BigOperators
open scoped Convolution

theorem energy_eventRoot_identity {n : ℕ} (Z : ℕ) {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (hn : normSquared ψ = 1)
    (hmin : ∀ (χ : Wavefunction n) (h : Gradient n),
      FormDomain χ h → normSquared χ = 1 → energy Z ψ g ≤ energy Z χ h)
    {F : Configuration n → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hF : ContDiff ℝ ∞ F) (hF0 : ∀ x, 0 ≤ F x) (hF1 : ∀ x, F x ≤ 1)
    (hsym : ∀ (p : Equiv.Perm (Fin n)) x, F (x ∘ p) = F x)
    (hgrad : ∀ x, (∑ i, ∑ a, (fderiv ℝ F x (coordinateDirection i a))^2) ≤
      K * (F x)^2 * (1-Real.log (F x))^5) :
    energy Z (multiplyWavefunction (fun x => Real.sqrt (F x)) ψ)
      (explicitMultiplyGradient (fun x => Real.sqrt (F x)) (eventRootDerivative F) ψ g) =
      energy Z ψ g * stateWeightedIntegral ψ F + explicitLocalizationError ψ (eventRootDerivative F) := by
  have hsq : SmoothMultiplier (fun x => (Real.sqrt (F x))^2) := by
    simpa only [Real.sq_sqrt (hF0 _)] using likelihood_smoothMultiplier hK hF hF0 hF1 hsym hgrad
  rw [energy_localization_explicit Z hd hsq
    (fun i a => (eventRootDerivative_measurable hF i a).aestronglyMeasurable)
    (fun i a => ⟨_, eventRootDerivative_bound hK hF0 hF1 hgrad i a⟩)
    (eventRoot_square_derivative hF0 hgrad), minimizer_multiplier_pairing Z hd hn hmin hsq]
  simp only [Real.sq_sqrt (hF0 _)]

theorem normSquared_eventRoot {n : ℕ} (ψ : Wavefunction n) {F : Configuration n → ℝ}
    (hF0 : ∀ x, 0 ≤ F x) :
    normSquared (multiplyWavefunction (fun x => Real.sqrt (F x)) ψ) =
      stateWeightedIntegral ψ F := by
  simp only [normSquared, norm_multiplyWavefunction_sq, Real.sq_sqrt (hF0 _), stateWeightedIntegral]

theorem eventTiltWavefunction_normalized {n : ℕ} (ψ : Wavefunction n) {F : Configuration n → ℝ}
    (hF0 : ∀ x, 0 ≤ F x) (hp : 0 < stateWeightedIntegral ψ F) :
    normSquared (eventTiltWavefunction ψ F) = 1 := by
  rw [eventTiltWavefunction, normSquared_scale, inv_pow, Real.sq_sqrt hp.le,
    normSquared_eventRoot ψ hF0, inv_mul_cancel₀ hp.ne']

theorem eventTiltWavefunction_raw_density {n : ℕ} (ψ : Wavefunction n) {F : Configuration n → ℝ}
    (hF0 : ∀ x, 0 ≤ F x) (hp : 0 < stateWeightedIntegral ψ F)
    (σ : Spins n) (x : Configuration n) :
    ‖eventTiltWavefunction ψ F σ x‖^2 =
      F x / stateWeightedIntegral ψ F * ‖ψ σ x‖^2 := by
  simp only [eventTiltWavefunction, scaleWavefunction, multiplyWavefunction,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow, Real.sq_sqrt hp.le,
    Real.sq_sqrt (hF0 x)]
  ring

theorem groundState_eventTilt {n : ℕ} (Z : ℕ) {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (hn : normSquared ψ = 1)
    (hmin : ∀ (χ : Wavefunction n) (h : Gradient n),
      FormDomain χ h → normSquared χ = 1 → energy Z ψ g ≤ energy Z χ h)
    {F : Configuration n → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hF : ContDiff ℝ ∞ F) (hF0 : ∀ x, 0 ≤ F x) (hF1 : ∀ x, F x ≤ 1)
    (hsym : ∀ (p : Equiv.Perm (Fin n)) x, F (x ∘ p) = F x)
    (hgrad : ∀ x, (∑ i, ∑ a, (fderiv ℝ F x (coordinateDirection i a))^2) ≤
      K * (F x)^2 * (1-Real.log (F x))^5)
    (hp : 0 < stateWeightedIntegral ψ F) :
    FormDomain (eventTiltWavefunction ψ F) (eventTiltGradient ψ g F) ∧
    normSquared (eventTiltWavefunction ψ F) = 1 ∧
    energy Z (eventTiltWavefunction ψ F) (eventTiltGradient ψ g F) ≤
      energy Z ψ g + K/8*(1+120*Real.exp 1)*(1-Real.log (stateWeightedIntegral ψ F))^5 := by
  refine ⟨(hd.eventRoot hK hF hF0 hF1 hsym hgrad).scale _,
    eventTiltWavefunction_normalized ψ hF0 hp, ?_⟩
  unfold eventTiltWavefunction eventTiltGradient
  rw [energy_scale, inv_pow, Real.sq_sqrt hp.le,
    energy_eventRoot_identity Z hd hn hmin hK hF hF0 hF1 hsym hgrad]
  calc
    _ ≤ (stateWeightedIntegral ψ F)⁻¹ *
        (energy Z ψ g * stateWeightedIntegral ψ F +
          K/8*(1+120*Real.exp 1)*stateWeightedIntegral ψ F*
            (1-Real.log (stateWeightedIntegral ψ F))^5) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (explicitLocalizationError_eventRoot_le hd hn hK hF hF0 hF1 hgrad hp))
        (inv_nonneg.mpr hp.le)
    _ = _ := by field_simp

theorem observationEventEnergyConstant_pos : 0 < observationEventEnergyConstant := by
  unfold observationEventEnergyConstant
  have := observationScoreConstant_pos
  positivity

theorem groundState_arrayEventTilt {H : Type*} [Fintype H] {n : ℕ} (Z : ℕ)
    {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (hn : normSquared ψ = 1)
    (hmin : ∀ (χ : Wavefunction n) (h : Gradient n),
      FormDomain χ h → normSquared χ = 1 → energy Z ψ g ≤ energy Z χ h)
    (ℓ : H → ℝ) (hℓ : ∀ h, 0 < ℓ h)
    {s : Set ((H × (Fin n × Fin 3)) → ℝ)} (hs : MeasurableSet s)
    (hsym : ∀ (p : Equiv.Perm (Fin n)) y, permuteObservationArray p y ∈ s ↔ y ∈ s)
    (hp : 0 < stateWeightedIntegral ψ (arrayEventLikelihood ℓ s)) :
    FormDomain (eventTiltWavefunction ψ (arrayEventLikelihood ℓ s))
      (eventTiltGradient ψ g (arrayEventLikelihood ℓ s)) ∧
    normSquared (eventTiltWavefunction ψ (arrayEventLikelihood ℓ s)) = 1 ∧
    energy Z (eventTiltWavefunction ψ (arrayEventLikelihood ℓ s))
      (eventTiltGradient ψ g (arrayEventLikelihood ℓ s)) ≤
      energy Z ψ g + observationEventEnergyConstant * observationWidthSquareSum ℓ *
        (1-Real.log (stateWeightedIntegral ψ (arrayEventLikelihood ℓ s)))^5 := by
  have hh := groundState_eventTilt Z hd hn hmin
    (mul_nonneg observationScoreConstant_pos.le (observationWidthSquareSum_nonneg ℓ))
    (arrayEventLikelihood_contDiff ℓ hs) (arrayEventLikelihood_nonneg ℓ hs)
    (arrayEventLikelihood_le_one ℓ hs)
    (arrayEventLikelihood_symmetric ℓ (fun h => (hℓ h).ne') hsym)
    (arrayEventLikelihood_gradient_bound ℓ hs) hp
  refine ⟨hh.1, hh.2.1, ?_⟩
  convert hh.2.2 using 1
  all_goals try with_reducible_and_instances rfl
  unfold observationEventEnergyConstant
  ring

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_LimitTheory_UniformGroundStateCountControl
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

theorem packetWidth_pos {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) (z : Position) : 0 < packetWidth c₁ r₀ s z := by
  unfold packetWidth
  have hmax : 0 < max ‖z‖ r₀ := lt_of_lt_of_le hr (le_max_right _ _)
  exact mul_pos (mul_pos hc hmax) (Real.rpow_pos_of_pos (lt_min hmax hs) _)

theorem packetKernel_eq_wavepacket_sq (g : Position → ℝ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (z y : Position) :
    packetKernel g c₁ r₀ s z y =
      ((packetWidth c₁ r₀ s z) ^ (-(3 / 2 : ℝ)) *
        g ((packetWidth c₁ r₀ s z)⁻¹ • (y-z))) ^ 2 := by
  have ht := (packetWidth_pos hc hr hs z).le
  rw [mul_pow]
  unfold packetKernel
  congr 1
  rw [← Real.rpow_natCast (_ ^ (-(3 / 2 : ℝ))) 2, ← Real.rpow_mul ht]
  norm_num

theorem packetKernel_nonneg (g : Position → ℝ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (z y : Position) :
    0 ≤ packetKernel g c₁ r₀ s z y := by
  rw [packetKernel_eq_wavepacket_sq g hc hr hs]
  positivity

theorem integral_packetKernel (g : Position → ℝ) (hg : (∫ y, g y ^ 2) = 1)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (z : Position) :
    (∫ y, packetKernel g c₁ r₀ s z y) = 1 := by
  have ht := packetWidth_pos hc hr hs z
  unfold packetKernel
  rw [integral_const_mul, integral_sub_right_eq_self
    (fun y : Position => (g ((packetWidth c₁ r₀ s z)⁻¹ • y)) ^ 2)]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume (fun y : Position => g y ^ 2) ht.le]
  simp only [Position, finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul, hg, mul_one]
  exact inv_mul_cancel₀ (pow_ne_zero _ ht.ne')

theorem integrable_packetKernel (g : Position → ℝ) (hg : (∫ y, g y ^ 2) = 1)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (z : Position) :
    Integrable (packetKernel g c₁ r₀ s z) := by
  by_contra hnot
  have hzero := integral_undef hnot
  rw [integral_packetKernel g hg hc hr hs z] at hzero
  exact one_ne_zero hzero

theorem packetWidth_le (c₁ r₀ s : ℝ) (hc : 0 ≤ c₁) (_hr : 0 < r₀)
    (hs : 0 < s) (z : Position) :
    packetWidth c₁ r₀ s z ≤ (c₁ * s ^ packetExponent) * max ‖z‖ r₀ := by
  unfold packetWidth
  calc
    c₁ * max ‖z‖ r₀ * min (max ‖z‖ r₀) s ^ packetExponent
      ≤ c₁ * max ‖z‖ r₀ * s ^ packetExponent := by
        apply mul_le_mul_of_nonneg_left
        · exact Real.rpow_le_rpow (le_min (le_max_of_le_left (norm_nonneg _)) hs.le)
            (min_le_right _ _) (by norm_num [packetExponent])
        · exact mul_nonneg hc (le_max_of_le_left (norm_nonneg _))
    _ = (c₁ * s ^ packetExponent) * max ‖z‖ r₀ := by ring

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_PhysicalBridge
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
noncomputable section
namespace NeutralAtom

lemma flattenConfiguration_measurePreserving (n : ℕ) :
    MeasurePreserving (flattenConfiguration n).toHomeomorph.toMeasurableEquiv :=
  (flattenConfiguration_symm_measurePreserving n).symm

lemma asH1_antisymmetric {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) : Coulomb.Antisymmetric (asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1) := by
  intro p s
  have H := (flattenConfiguration_symm_measurePreserving n).quasiMeasurePreserving.ae (hd.1 p s)
  exact H

lemma fromH1_mass {n : ℕ} (ψ : Coulomb.H1Vector n) :
    normSquared (fromH1Wave ψ) = Coulomb.mass ψ := by
  unfold normSquared Coulomb.mass fromH1Wave
  apply Finset.sum_congr rfl
  intro s _
  exact (flattenConfiguration_measurePreserving n).integral_comp' (fun x => ‖ψ.value s x‖^2)

lemma asH1_mass {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hw : HasWeakGradient ψ g) (hψ : ∀ σ, MemLp (ψ σ) 2 volume)
    (hg : ∀ σ i a, MemLp (g σ i a) 2 volume) :
    Coulomb.mass (asH1 ψ g hw hψ hg) = normSquared ψ := by
  unfold normSquared Coulomb.mass asH1
  apply Finset.sum_congr rfl
  intro s _
  exact (flattenConfiguration_symm_measurePreserving n).integral_comp' (fun x => ‖ψ s x‖^2)

lemma coulombPotential_flatten {n : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) (x : Configuration n) :
    coulombPotential Z x = -Coulomb.nuclearPotential (Coulomb.atom Z hZ)
      (flattenConfiguration n x) + Coulomb.pairPotential (flattenConfiguration n x) := by
  classical
  simp [coulombPotential,Coulomb.nuclearPotential,Coulomb.pairPotential,Coulomb.attraction,
    Coulomb.atom,Coulomb.coulombKernel,Finset.sum_filter,Finset.mul_sum,neg_mul]

lemma fromH1_energy {n : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) (ψ : Coulomb.H1Vector n) :
    energy Z (fromH1Wave ψ) (fromH1Gradient ψ) = Coulomb.form (Coulomb.atom Z hZ) ψ := by
  have hK : (∑ s : Spins n, ∑ i : Fin n, ∑ a : Fin 3,
      ∫ x : Configuration n, ‖fromH1Gradient ψ s i a x‖^2) =
      ∑ s : Coulomb.Spins n, ∑ ia : Fin n × Fin 3,
        ∫ x : Coulomb.Configuration n, ‖ψ.gradient s ia x‖^2 := by
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro a _
    exact (flattenConfiguration_measurePreserving n).integral_comp' (fun x => ‖ψ.gradient s (i,a) x‖^2)
  have hV (s : Spins n) :
      (∫ x : Configuration n, coulombPotential Z x * ‖fromH1Wave ψ s x‖^2) =
      -(∫ x, Coulomb.nuclearPotential (Coulomb.atom Z hZ) x * ‖ψ.value s x‖^2) +
        ∫ x, Coulomb.pairPotential x * ‖ψ.value s x‖^2 := by
    simp_rw [coulombPotential_flatten Z hZ]
    change (∫ x, (-Coulomb.nuclearPotential (Coulomb.atom Z hZ) (flattenConfiguration n x) +
      Coulomb.pairPotential (flattenConfiguration n x)) * ‖ψ.value s (flattenConfiguration n x)‖^2) = _
    calc
      _ = ∫ x, (-Coulomb.nuclearPotential (Coulomb.atom Z hZ) x + Coulomb.pairPotential x) * ‖ψ.value s x‖^2 :=
        (flattenConfiguration_measurePreserving n).integral_comp'
          (fun x => (-Coulomb.nuclearPotential (Coulomb.atom Z hZ) x + Coulomb.pairPotential x) * ‖ψ.value s x‖^2)
      _ = _ := ?_

    simp_rw [add_mul,neg_mul]
    have hn : Integrable (fun x => -(Coulomb.nuclearPotential (Coulomb.atom Z hZ) x * ‖ψ.value s x‖^2)) :=
      (ψ.nuclear_integrable (Coulomb.atom Z hZ) s).neg
    have hp : Integrable (fun x => Coulomb.pairPotential x * ‖ψ.value s x‖^2) := ψ.pair_integrable s
    rw [integral_add hn hp, integral_neg]
  unfold energy Coulomb.form Coulomb.kinetic Coulomb.nuclearEnergy Coulomb.pairEnergy
  rw [hK]
  simp_rw [hV, Finset.sum_add_distrib,Finset.sum_neg_distrib]
  unfold Coulomb.nuclearPotential Coulomb.pairPotential
  ring

lemma asH1_energy {n : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction n} {g : Gradient n}
    (hw : HasWeakGradient ψ g) (hψ : ∀ σ, MemLp (ψ σ) 2 volume)
    (hg : ∀ σ i a, MemLp (g σ i a) 2 volume) :
    Coulomb.form (Coulomb.atom Z hZ) (asH1 ψ g hw hψ hg) = energy Z ψ g := by
  exact (fromH1_energy Z hZ (asH1 ψ g hw hψ hg)).symm

end NeutralAtom

end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_ObservationAtomic
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

lemma asH1_potentialForm {n : ℕ} (ψ : Wavefunction n) (g : Gradient n)
    (hw : HasWeakGradient ψ g) (hψ : ∀ σ, MemLp (ψ σ) 2 volume)
    (hg : ∀ σ i a, MemLp (g σ i a) 2 volume) (B : Coulomb.Configuration n → ℝ) :
    Coulomb.potentialForm B (asH1 ψ g hw hψ hg) =
      stateWeightedIntegral ψ (fun x => B (flattenConfiguration n x)) := by
  unfold Coulomb.potentialForm stateWeightedIntegral
  apply Finset.sum_congr rfl
  intro σ _
  change (∫ x, B x*‖ψ σ ((flattenConfiguration n).symm x)‖^2) = _
  have H := (flattenConfiguration_symm_measurePreserving n).integral_comp'
    (fun x => B (flattenConfiguration n x)*‖ψ σ x‖^2)
  change (∫ x, B (flattenConfiguration n ((flattenConfiguration n).symm x))*
    ‖ψ σ ((flattenConfiguration n).symm x)‖^2) = _ at H
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using H

lemma eventTilt_stateWeightedIntegral {n : ℕ} (ψ : Wavefunction n)
    {F : Configuration n → ℝ} (hF : ∀ x, 0 ≤ F x)
    (hp : 0 < stateWeightedIntegral ψ F) (B : Configuration n → ℝ) :
    stateWeightedIntegral (eventTiltWavefunction ψ F) B =
      (stateWeightedIntegral ψ F)⁻¹ * stateWeightedIntegral ψ (fun x => F x*B x) := by
  unfold stateWeightedIntegral
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [eventTiltWavefunction_raw_density ψ hF hp]
  simp only [stateWeightedIntegral]
  ring

theorem atomic_arrayEvent_state {H : Type*} [Fintype H] {n : ℕ}
    (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (hn : normSquared ψ=1)
    (hmin : ∀ (χ : Wavefunction n) (h : Gradient n),
      FormDomain χ h → normSquared χ=1 → energy Z ψ g ≤ energy Z χ h)
    {E D₀ : ℝ} (hbase : energy Z ψ g ≤ E+D₀)
    (ℓ : H → ℝ) (hℓ : ∀ h, 0 < ℓ h)
    {s : Set ((H × (Fin n × Fin 3)) → ℝ)} (hs : MeasurableSet s)
    (hsym : ∀ (p : Equiv.Perm (Fin n)) y, permuteObservationArray p y∈s ↔ y∈s)
    (hp : 0 < stateWeightedIntegral ψ (arrayEventLikelihood ℓ s)) :
    ∃ u : Coulomb.H1Vector n, Coulomb.Antisymmetric u ∧ Coulomb.mass u=1 ∧
      Coulomb.form (Coulomb.atom Z hZ) u ≤ E+(D₀+observationEventEnergyConstant*
        observationWidthSquareSum ℓ*(1-Real.log (stateWeightedIntegral ψ (arrayEventLikelihood ℓ s)))^5) ∧
      ∀ B : Coulomb.Configuration n → ℝ,
        Coulomb.potentialForm B u = (stateWeightedIntegral ψ (arrayEventLikelihood ℓ s))⁻¹*
          stateWeightedIntegral ψ (fun x => arrayEventLikelihood ℓ s x*B (flattenConfiguration n x)) := by
  obtain ⟨hdom,hmass,henergy⟩ := groundState_arrayEventTilt Z hd hn hmin ℓ hℓ hs hsym hp
  let u := asH1 (eventTiltWavefunction ψ (arrayEventLikelihood ℓ s))
    (eventTiltGradient ψ g (arrayEventLikelihood ℓ s)) hdom.2.1 hdom.2.2.1 hdom.2.2.2.1
  refine ⟨u,asH1_antisymmetric hdom,(asH1_mass ..).trans hmass,?_,?_⟩
  · change Coulomb.form (Coulomb.atom Z hZ) (asH1 ..) ≤ _
    rw [asH1_energy Z hZ]
    linarith
  · intro B
    rw [asH1_potentialForm,eventTilt_stateWeightedIntegral ψ (arrayEventLikelihood_nonneg ℓ hs) hp]

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_PacketWidthScalar
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set
namespace NeutralAtom

theorem clamped_width_scalar_lipschitz {w s u v : ℝ}
    (hw : 0  ≤  w) (hs : 0  <  s) (hu : 0  <  u) (hv : 0  <  v) :
    |u * (min u s)^w - v * (min v s)^w|  ≤
      (1+w)*s^w*|u-v| := by
  have hbelow {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ s) :
      |y*(min y s)^w-x*(min x s)^w|  ≤  (1+w)*s^w*(y-x) := by
    have href : ∀ z ∈ Icc x y,
        HasDerivWithinAt (fun z : ℝ => z^(w+1)) ((w+1)*z^w) (Icc x y) z := by
      intro z hz
      simpa only [add_sub_cancel_right] using (Real.hasDerivAt_rpow_const (p := w+1) (Or.inl (ne_of_gt (hx.trans_le hz.1)))).hasDerivWithinAt (s := Icc x y)
    have hbd : ∀ z ∈ Icc x y, ‖(w+1)*z^w‖  ≤  (1+w)*s^w := by
      intro z hz
      rw [Real.norm_of_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg (hx.le.trans hz.1) _))]
      calc
        (w+1)*z^w  ≤  (w+1)*s^w := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (hx.le.trans hz.1) (hz.2.trans hy) hw) (by linarith)
        _ = (1+w)*s^w := by ring
    have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le href hbd
      (convex_Icc x y) (show x ∈ Icc x y from ⟨le_rfl,hxy⟩)
      (show y ∈ Icc x y from ⟨hxy,le_rfl⟩)
    rw [Real.rpow_add_one (ne_of_gt (hx.trans_le hxy)), Real.rpow_add_one hx.ne',
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hxy)] at hh
    simpa only [min_eq_left hy, min_eq_left (hxy.trans hy), mul_comm] using hh
  have hordered {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
      |y*(min y s)^w-x*(min x s)^w|  ≤  (1+w)*s^w*(y-x) := by
    by_cases hy : y ≤ s
    · exact hbelow hx hxy hy
    by_cases hxs : s ≤ x
    · rw [min_eq_right hxs, min_eq_right (hxs.trans hxy), ←sub_mul,
        abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hxy) (Real.rpow_nonneg hs.le _))]
      have hw0 := mul_nonneg hw (mul_nonneg (Real.rpow_nonneg hs.le w) (sub_nonneg.mpr hxy))
      nlinarith
    · have hxle : x  ≤  s := le_of_not_ge hxs
      have hsy : s  ≤  y := le_of_not_ge hy
      have hh := hbelow hx hxle le_rfl
      rw [min_self, min_eq_left hxle] at hh
      have he : y*s^w - x*x^w = (y-s)*s^w+(s*s^w-x*x^w) := by ring
      rw [min_eq_right hsy, min_eq_left hxle,he]
      calc
        |(y-s)*s^w+(s*s^w-x*x^w)|  ≤  |(y-s)*s^w|+|s*s^w-x*x^w| := abs_add_le _ _
        _  ≤  (y-s)*s^w+(1+w)*s^w*(s-x) := by
          rw [abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hsy) (Real.rpow_nonneg hs.le _))]
          exact add_le_add_right hh _
        _  ≤  (1+w)*s^w*(y-x) := by
          have hw0 := mul_nonneg hw (mul_nonneg (Real.rpow_nonneg hs.le w) (sub_nonneg.mpr hsy))
          nlinarith
  rcases le_total u v with huv | hvu
  · rw [abs_sub_comm,abs_of_nonpos (sub_nonpos.mpr huv)]
    simpa only [neg_sub] using hordered hu huv
  · rw [abs_of_nonneg (sub_nonneg.mpr hvu)]
    exact hordered hv hvu
end NeutralAtom

end
open MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace NeutralAtom

theorem continuous_packetWidth (c₁ r₀ s : ℝ) : Continuous (packetWidth c₁ r₀ s) := by
  unfold packetWidth
  fun_prop (disch := norm_num [packetExponent])

theorem packetWidth_lipschitz {c r₀ s : ℝ} (hc : 0 ≤ c)
    (hr : 0 < r₀) (hs : 0 < s) (z z' : Position) :
    |packetWidth c r₀ s z-packetWidth c r₀ s z'| ≤
      (c*(1+packetExponent)*s^packetExponent)*‖z-z'‖ := by
  have h := clamped_width_scalar_lipschitz (w := packetExponent) (u := max ‖z‖ r₀) (v := max ‖z'‖ r₀) (by norm_num [packetExponent]) hs
    (hr.trans_le (le_max_right _ _)) (hr.trans_le (le_max_right _ _))
  have hm : |max ‖z‖ r₀-max ‖z'‖ r₀| ≤ ‖z-z'‖ := by
    calc
      _ ≤ max |‖z‖-‖z'‖| |r₀-r₀| := abs_max_sub_max_le_max _ _ _ _
      _ = |‖z‖-‖z'‖| := by simp
      _ ≤ ‖z-z'‖ := abs_norm_sub_norm_le _ _
  unfold packetWidth
  rw [show c*max ‖z‖ r₀*(min (max ‖z‖ r₀) s)^packetExponent-
      c*max ‖z'‖ r₀*(min (max ‖z'‖ r₀) s)^packetExponent =
      c*(max ‖z‖ r₀*(min (max ‖z‖ r₀) s)^packetExponent-
      max ‖z'‖ r₀*(min (max ‖z'‖ r₀) s)^packetExponent) by ring,
    abs_mul,abs_of_nonneg hc]
  calc
    _ ≤ c*((1+packetExponent)*s^packetExponent*|max ‖z‖ r₀-max ‖z'‖ r₀|) :=
      mul_le_mul_of_nonneg_left h hc
    _ ≤ (c*(1+packetExponent)*s^packetExponent)*‖z-z'‖ := by
      have hh := mul_le_mul_of_nonneg_left hm
        (show 0 ≤ c*(1+packetExponent)*s^packetExponent from
          mul_nonneg (mul_nonneg hc (by norm_num [packetExponent])) (Real.rpow_nonneg hs.le _))
      simpa only [mul_assoc] using hh

end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ConditionalDensity
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace NeutralAtom

theorem continuous_packetKernel {g : Position → ℝ} (hg : Continuous g)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) :
    Continuous (fun zy : Position × Position => packetKernel g c₁ r₀ s zy.1 zy.2) := by
  have ht : Continuous (fun zy : Position × Position => packetWidth c₁ r₀ s zy.1) :=
    (continuous_packetWidth c₁ r₀ s).comp continuous_fst
  have htne : ∀ zy : Position × Position, packetWidth c₁ r₀ s zy.1 ≠ 0 :=
    fun zy => (packetWidth_pos hc hr hs zy.1).ne'
  unfold packetKernel
  exact ((ht.pow 3).inv₀ (fun zy => pow_ne_zero _ (htne zy))).mul
    ((hg.comp ((ht.inv₀ htne).smul (continuous_snd.sub continuous_fst))).pow 2)

theorem rawPacketDensity_nonneg {n : ℕ} (g : Position → ℝ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (x : Configuration n) (y : Position) :
    0 ≤ rawPacketDensity g c₁ r₀ s x y :=
  Finset.sum_nonneg (fun i _ => packetKernel_nonneg g hc hr hs (x i) y)

theorem rawPacketDensity_integrable {n : ℕ} (g : Position → ℝ) (hgnorm : (∫ y, g y^2)=1)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (x : Configuration n) :
    Integrable (rawPacketDensity g c₁ r₀ s x) :=
  integrable_finsetSum _ (fun i _ => integrable_packetKernel g hgnorm hc hr hs (x i))

theorem rawPacketDensity_mass {n : ℕ} (g : Position → ℝ) (hgnorm : (∫ y, g y^2)=1)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (x : Configuration n) :
    (∫ y, rawPacketDensity g c₁ r₀ s x y) = n := by
  unfold rawPacketDensity
  rw [integral_finsetSum _ (fun i _ => integrable_packetKernel g hgnorm hc hr hs (x i))]
  simp only [integral_packetKernel g hgnorm hc hr hs, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem continuous_rawPacketDensity {n : ℕ} {g : Position → ℝ} (hg : Continuous g)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) :
    Continuous (fun xy : Configuration n × Position => rawPacketDensity g c₁ r₀ s xy.1 xy.2) := by
  have hi : ∀ i : Fin n, Continuous (fun xy : Configuration n × Position =>
      packetKernel g c₁ r₀ s (xy.1 i) xy.2) := by
    intro i
    have hh : Continuous (fun xy : Configuration n × Position => xy.1 i) :=
      (continuous_apply i).comp continuous_fst
    have hhpair : Continuous (fun xy : Configuration n × Position => (xy.1 i,xy.2)) :=
      hh.prodMk continuous_snd
    change Continuous ((fun zy : Position × Position => packetKernel g c₁ r₀ s zy.1 zy.2) ∘
      (fun xy : Configuration n × Position => (xy.1 i,xy.2)))
    exact (continuous_packetKernel hg hc hr hs).comp hhpair
  exact continuous_finsetSum Finset.univ (fun i _ => hi i)

theorem rawPacketDensity_prod_integrable {n : ℕ} {g : Position → ℝ} (hg : Continuous g)
    (hgnorm : (∫ y, g y^2)=1) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    (ν : Measure (Configuration n)) [IsFiniteMeasure ν] :
    Integrable (fun xy : Configuration n × Position => rawPacketDensity g c₁ r₀ s xy.1 xy.2)
      (ν.prod volume) := by
  apply (integrable_prod_iff (continuous_rawPacketDensity hg hc hr hs).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (rawPacketDensity_integrable g hgnorm hc hr hs)
  · have he : (fun x : Configuration n => ∫ y, ‖rawPacketDensity g c₁ r₀ s x y‖) =
        (fun _ => (n : ℝ)) := by
      funext x
      simp only [Real.norm_eq_abs, abs_of_nonneg (rawPacketDensity_nonneg g hc hr hs x _),
        rawPacketDensity_mass g hgnorm hc hr hs]
    rw [he]
    exact integrable_const _

theorem mixturePacketDensity_integrable {n : ℕ} {g : Position → ℝ} (hg : Continuous g)
    (hgnorm : (∫ y, g y^2)=1) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    (ν : Measure (Configuration n)) [IsFiniteMeasure ν] :
    Integrable (mixturePacketDensity ν g c₁ r₀ s) :=
  (rawPacketDensity_prod_integrable hg hgnorm hc hr hs ν).integral_prod_right

theorem mixturePacketDensity_nonneg {n : ℕ} (ν : Measure (Configuration n))
    (g : Position → ℝ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    (y : Position) : 0 ≤ mixturePacketDensity ν g c₁ r₀ s y :=
  integral_nonneg (fun x => rawPacketDensity_nonneg g hc hr hs x y)

theorem packetWidth_lower {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (z : Position) :
    c₁*r₀*(min r₀ s)^packetExponent ≤ packetWidth c₁ r₀ s z := by
  unfold packetWidth
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (le_max_right _ _) hc.le
  · exact Real.rpow_le_rpow (lt_min hr hs).le
      (min_le_min (le_max_right _ _) le_rfl) (by norm_num [packetExponent])
  · exact Real.rpow_nonneg (lt_min hr hs).le _
  · exact mul_nonneg hc.le (hr.le.trans (le_max_right _ _))

theorem compact_packet_function_bound {g : Position → ℝ} (hg : Continuous g)
    (hgs : HasCompactSupport g) : ∃ A : ℝ, 0 ≤ A ∧ ∀ x, g x^2 ≤ A := by
  obtain ⟨A,hA⟩ := ((hgs.isCompact_range hg).image (continuous_id.pow 2)).bddAbove
  refine ⟨A, (sq_nonneg (g 0)).trans (hA ⟨g 0, ⟨0,rfl⟩,rfl⟩), ?_⟩
  intro x
  exact hA ⟨g x,⟨x,rfl⟩,rfl⟩

theorem packetKernel_bound {g : Position → ℝ} {A c₁ r₀ s : ℝ}
    (_hA : 0 ≤ A) (hg : ∀ x, g x^2 ≤ A)
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (z y : Position) :
    packetKernel g c₁ r₀ s z y ≤ (c₁*r₀*(min r₀ s)^packetExponent)^(-3:ℤ)*A := by
  have hp : 0 < c₁*r₀*(min r₀ s)^packetExponent := by positivity
  have hh := packetWidth_lower hc hr hs z
  have hinv := inv_anti₀ (pow_pos hp 3) (pow_le_pow_left₀ hp.le hh 3)
  change (packetWidth c₁ r₀ s z^3)⁻¹*g _^2 ≤ _
  rw [zpow_neg]
  exact mul_le_mul hinv (hg _) (sq_nonneg _) (by positivity)

theorem rawPacketDensity_bound {n : ℕ} {g : Position → ℝ} {A c₁ r₀ s : ℝ}
    (hA : 0 ≤ A) (hg : ∀ x, g x^2 ≤ A)
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (x : Configuration n) (y : Position) :
    rawPacketDensity g c₁ r₀ s x y ≤
      n*((c₁*r₀*(min r₀ s)^packetExponent)^(-3:ℤ)*A) := by
  calc
    _ ≤ ∑ _i : Fin n, (c₁*r₀*(min r₀ s)^packetExponent)^(-3:ℤ)*A :=
      Finset.sum_le_sum (fun i _ => packetKernel_bound hA hg hc hr hs (x i) y)
    _ = _ := by simp

theorem rawPacketDensity_integrable_configuration {n : ℕ} {g : Position → ℝ}
    (hg : Continuous g) (hgs : HasCompactSupport g) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    (ν : Measure (Configuration n)) [IsFiniteMeasure ν] (y : Position) :
    Integrable (fun x => rawPacketDensity g c₁ r₀ s x y) ν := by
  obtain ⟨A,hA,hAb⟩ := compact_packet_function_bound hg hgs
  have hm : AEStronglyMeasurable (fun x => rawPacketDensity g c₁ r₀ s x y) ν :=
    ((continuous_rawPacketDensity hg hc hr hs).comp
      (continuous_id.prodMk (continuous_const (y := y)))).aestronglyMeasurable
  apply (integrable_const (n*((c₁*r₀*(min r₀ s)^packetExponent)^(-3:ℤ)*A))).mono' hm
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (rawPacketDensity_nonneg g hc hr hs x y)]
    using rawPacketDensity_bound hA hAb hc hr hs x y

theorem mixturePacketDensity_bounded {n : ℕ} {g : Position → ℝ}
    (hg : Continuous g) (hgs : HasCompactSupport g) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (ν : Measure (Configuration n)) [IsProbabilityMeasure ν] y,
      mixturePacketDensity ν g c₁ r₀ s y ≤ A := by
  obtain ⟨A,hA,hAb⟩ := compact_packet_function_bound hg hgs
  let C := n*((c₁*r₀*(min r₀ s)^packetExponent)^(-3:ℤ)*A)
  have hw : 0 < c₁*r₀*(min r₀ s)^packetExponent := by positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro ν hν y
  have hh := integral_mono (rawPacketDensity_integrable_configuration hg hgs hc hr hs ν y)
    (integrable_const C) (fun x => rawPacketDensity_bound hA hAb hc hr hs x y)
  simpa only [mixturePacketDensity, integral_const, probReal_univ, one_smul] using hh

theorem conditionalPacketDensity_nonneg {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    {n : ℕ} (P : Measure Ω) [IsFiniteMeasure P]
    (raw : Ω → Configuration n) (obs : Ω → B)
    (g : Position → ℝ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    (datum : B) (y : Position) : 0 ≤ conditionalPacketDensity P raw obs g c₁ r₀ s datum y :=
  mixturePacketDensity_nonneg _ g hc hr hs y

theorem conditionalPacketDensity_bounded {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    {n : ℕ} (P : Measure Ω) [IsFiniteMeasure P]
    (raw : Ω → Configuration n) (obs : Ω → B)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ datum y, conditionalPacketDensity P raw obs g c₁ r₀ s datum y ≤ A := by
  obtain ⟨A,hA,h⟩ := mixturePacketDensity_bounded (n := n) hg hgs hc hr hs
  exact ⟨A,hA,fun datum y => h (ProbabilityTheory.condDistrib raw obs P datum) y⟩

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ConditionalMatching
attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff
namespace NeutralAtom

theorem measurable_forgetOrder {n : ℕ} : Measurable (forgetOrder (n := n)) :=
  measurable_iff_le_map.mpr le_rfl

theorem forgetOrder_permutation {n : ℕ} (x : Configuration n) (p : Equiv.Perm (Fin n)) :
    forgetOrder (x ∘ p) = forgetOrder x := by
  apply Eq.symm
  exact Quotient.sound ⟨p,rfl⟩

theorem observationLaw_rawProjection {n J : ℕ} (ν : Measure (Configuration n)) :
    MeasurePreserving Prod.fst (observationLaw J ν) ν := measurePreserving_fst

theorem observationNoiseVector_coordinate (v : Fin 3 → ℝ) (a : Fin 3) :
    observationNoiseVector v a = v a := by
  simp [observationNoiseVector, Pi.single_apply]

theorem continuous_observationNoiseVector : Continuous observationNoiseVector := by
  unfold observationNoiseVector
  exact continuous_finsetSum Finset.univ (fun a _ => (continuous_apply a).smul continuous_const)

theorem measurable_observedOrdered {n J : ℕ} (r : Fin J → ℝ) (j : Fin J) :
    Measurable (observedOrdered (n := n) r j) := by
  apply Measurable.of_eval
  intro i
  have hn : Measurable (fun sample : ObservationSample n J => sample.2 j i) :=
    (measurable_pi_apply i).comp ((measurable_pi_apply j).comp measurable_snd)
  exact ((measurable_pi_apply i).comp measurable_fst).add
    ((continuous_observationNoiseVector.measurable.comp hn).const_smul ((r j)^(101/100 : ℝ)))

theorem measurable_observedArray {n J : ℕ} (r : Fin J → ℝ) (j : Fin J) :
    Measurable (observedArray (n := n) r j) :=
  measurable_forgetOrder.comp (measurable_observedOrdered r j)

theorem measurable_tailObservation {n J : ℕ} (r : Fin J → ℝ) (j : ℕ) :
    Measurable (tailObservation (n := n) r j) := by
  apply Measurable.of_eval
  intro k
  by_cases hj : j ≤ k.val
  · simpa only [tailObservation, ite_eq_left hj] using measurable_observedArray r k
  · simpa only [tailObservation, ite_eq_right hj] using
      (measurable_const : Measurable (fun _ : ObservationSample n J => forgetOrder (0 : Configuration n)))

end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_OriginalPotentialTower
attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace NeutralAtom

theorem rawPacketPotential_uniform {n : ℕ} {g : Position → ℝ}
    (hg : Continuous g) (hgs : HasCompactSupport g) (hm : (∫ z, g z^2)=1)
    {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s) :
    ∃ B : ℝ, 0≤B ∧ ∀ (x : Configuration n) (y : Position),
      Integrable (fun z => coulombKernel (y-z)*rawPacketDensity g c r₀ s x z) ∧
      0≤potentialOf (rawPacketDensity g c r₀ s x) y ∧
      potentialOf (rawPacketDensity g c r₀ s x) y≤B := by
  obtain ⟨A,hA,hAb⟩ := compact_packet_function_bound hg hgs
  let M : ℝ := n*((c*r₀*(min r₀ s)^packetExponent)^(-3:ℤ)*A)
  have hM : 0≤M := by dsimp [M]; positivity
  refine ⟨2*Real.pi*M+n,by positivity,?_⟩
  intro x y
  have hρ := rawPacketDensity_integrable g hm hc hr hs x
  have hρm : Measurable (rawPacketDensity g c r₀ s x) :=
    ((continuous_rawPacketDensity hg hc hr hs).comp
      ((continuous_const (y := x)).prodMk continuous_id)).measurable
  have hρ0 := rawPacketDensity_nonneg g hc hr hs x
  have hρM : ∀ z,rawPacketDensity g c r₀ s x z≤M :=
    rawPacketDensity_bound hA hAb hc hr hs x
  refine ⟨Coulomb.coulomb_convolution_integrable hρ hρm hρ0 hρM
    (by norm_num : (0:ℝ)<1) y,integral_nonneg (fun z =>
      mul_nonneg (coulombKernel_nonneg _) (hρ0 z)),?_⟩
  simpa [potentialOf,coulombKernel,Coulomb.coulombKernel,rawPacketDensity_mass g hm hc hr hs] using
    Coulomb.coulomb_convolution_bound hρ hρm hρ0 hρM (by norm_num : (0:ℝ)<1) y

lemma measurable_rawPacketPotential {n : ℕ} {g : Position → ℝ} (hg : Continuous g)
    {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s) (y : Position) :
    Measurable (fun x : Configuration n => potentialOf (rawPacketDensity g c r₀ s x) y) := by
  have hi : Measurable (fun xz : Configuration n × Position =>
      coulombKernel (y-xz.2)*rawPacketDensity g c r₀ s xz.1 xz.2) :=
    (measurable_coulombKernel.comp (measurable_const.sub measurable_snd)).mul
      (continuous_rawPacketDensity hg hc hr hs).measurable
  exact hi.stronglyMeasurable.integral_prod_right'.measurable

lemma integrable_rawPacketPotential {n : ℕ} {g : Position → ℝ}
    (hg : Continuous g) (hgs : HasCompactSupport g) (hm : (∫ z,g z^2)=1)
    {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s)
    (ν : Measure (Configuration n)) [IsFiniteMeasure ν] (y : Position) :
    Integrable (fun x => potentialOf (rawPacketDensity g c r₀ s x) y) ν := by
  obtain ⟨B,hB,H⟩ := rawPacketPotential_uniform (n := n) hg hgs hm hc hr hs
  apply (integrable_const B).mono' (measurable_rawPacketPotential hg hc hr hs y).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by simpa [Real.norm_of_nonneg (H x y).2.1] using (H x y).2.2)

theorem mixturePacketPotential {n : ℕ} {g : Position → ℝ}
    (hg : Continuous g) (hgs : HasCompactSupport g) (hm : (∫ z,g z^2)=1)
    {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s)
    (ν : Measure (Configuration n)) [IsFiniteMeasure ν] (y : Position) :
    potentialOf (mixturePacketDensity ν g c r₀ s) y =
      ∫ x, potentialOf (rawPacketDensity g c r₀ s x) y ∂ν := by
  obtain ⟨B,hB,H⟩ := rawPacketPotential_uniform (n := n) hg hgs hm hc hr hs
  have hmeas : Measurable (fun xz : Configuration n × Position =>
      coulombKernel (y-xz.2)*rawPacketDensity g c r₀ s xz.1 xz.2) :=
    (measurable_coulombKernel.comp (measurable_const.sub measurable_snd)).mul
      (continuous_rawPacketDensity hg hc hr hs).measurable
  have hi : Integrable (fun xz : Configuration n × Position =>
      coulombKernel (y-xz.2)*rawPacketDensity g c r₀ s xz.1 xz.2) (ν.prod volume) := by
    apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall (fun x => (H x y).1),?_⟩
    have he : (fun x : Configuration n => ∫ z, ‖coulombKernel (y-z)*rawPacketDensity g c r₀ s x z‖)=
        fun x => potentialOf (rawPacketDensity g c r₀ s x) y := by
      funext x
      simp only [potentialOf,Real.norm_of_nonneg (mul_nonneg (coulombKernel_nonneg _) (rawPacketDensity_nonneg g hc hr hs x _))]
    rw [he]
    exact integrable_rawPacketPotential hg hgs hm hc hr hs ν y
  change (∫ z, coulombKernel (y-z)*(∫ x,rawPacketDensity g c r₀ s x z ∂ν))=_
  simp_rw [←integral_const_mul]
  exact integral_integral_swap hi.swap

theorem conditionalPacketPotential_eq_condExp {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure (Configuration n)) [IsFiniteMeasure ν]
    {raw : Ω → Configuration n} {obs : Ω → B}
    (hraw : MeasurePreserving raw P ν) (hobs : Measurable obs)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g)
    (hm : (∫ z,g z^2)=1) {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s)
    (y : Position) :
    (fun sample => potentialOf (conditionalPacketDensity P raw obs g c r₀ s (obs sample)) y) =ᵐ[P]
      P[fun sample => potentialOf (rawPacketDensity g c r₀ s (raw sample)) y |
        MeasurableSpace.comap obs inferInstance] := by
  have he := ProbabilityTheory.condExp_ae_eq_integral_condDistrib hobs hraw.measurable.aemeasurable
    (measurable_rawPacketPotential hg hc hr hs y).stronglyMeasurable
    (hraw.integrable_comp_of_integrable (integrable_rawPacketPotential hg hgs hm hc hr hs ν y))
  exact (he.trans (Eventually.of_forall (fun sample =>
    (mixturePacketPotential hg hgs hm hc hr hs (ProbabilityTheory.condDistrib raw obs P (obs sample)) y).symm))).symm

theorem conditionalPacketPotential_event_tower {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure (Configuration n)) [IsFiniteMeasure ν]
    {raw : Ω → Configuration n} {obs : Ω → B}
    (hraw : MeasurePreserving raw P ν) (hobs : Measurable obs)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g)
    (hm : (∫ z,g z^2)=1) {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s)
    {A : Set Ω} (hA : MeasurableSet[MeasurableSpace.comap obs inferInstance] A)
    (y : Position) :
    (∫ sample in A, potentialOf (conditionalPacketDensity P raw obs g c r₀ s (obs sample)) y ∂P)=
      ∫ sample in A, potentialOf (rawPacketDensity g c r₀ s (raw sample)) y ∂P := by
  have hle := measurable_iff_comap_le.mp hobs
  have he := conditionalPacketPotential_eq_condExp P ν hraw hobs hg hgs hm hc hr hs y
  rw [setIntegral_congr_ae (hle _ hA) (he.mono (fun x hx _ => hx))]
  exact setIntegral_condExp hle
    (hraw.integrable_comp_of_integrable (integrable_rawPacketPotential hg hgs hm hc hr hs ν y)) hA

theorem physical_observation_potential_tower {n J : ℕ}
    (ν : Measure (Configuration n)) [IsProbabilityMeasure ν]
    (r : Fin J → ℝ) (j : ℕ) {g : Position → ℝ}
    (hg : Continuous g) (hgs : HasCompactSupport g) (hm : (∫ z,g z^2)=1)
    {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s)
    {A : Set (ObservationSample n J)} (hA : MeasurableSet[observationSigma r j] A)
    (y : Position) :
    (∫ sample in A, potentialOf
      (conditionalPacketDensity (observationLaw J ν) Prod.fst (tailObservation r j)
        g c r₀ s (tailObservation r j sample)) y ∂observationLaw J ν)=
      ∫ sample in A, potentialOf (rawPacketDensity g c r₀ s sample.1) y ∂observationLaw J ν :=
  conditionalPacketPotential_event_tower (observationLaw J ν) ν (observationLaw_rawProjection ν)
    (measurable_tailObservation r j) hg hgs hm hc hr hs hA y

end NeutralAtom

end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ObservationMatching
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
namespace NeutralAtom

lemma measurable_observationArrayPositions {H : Type*} {n : ℕ} (h : H) :
    Measurable (@observationArrayPositions H n h) := by
  unfold observationArrayPositions
  fun_prop

end NeutralAtom

end
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PhysicalLikelihoodBridge
attribute [-instance] _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
namespace NeutralAtom

lemma rawExpectation_eq_stateWeightedIntegral {n : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) {F : Configuration n → ℝ}
    (hF : Measurable F) {C : ℝ} (hC : ∀ x, ‖F x‖≤C) :
    rawExpectation ψ F=stateWeightedIntegral ψ F := by
  unfold rawExpectation configurationDensity stateWeightedIntegral
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum _ (fun σ _ =>
    (hψ σ).norm.integrable_sq.bdd_mul hF.aestronglyMeasurable
      (Eventually.of_forall hC))

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PhysicalRetainedLikelihood
attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace NeutralAtom

lemma flattenIndexedNoise_preserving (n : ℕ) (H : Type*) [Fintype H] :
    MeasurePreserving (flattenIndexedNoise n H)
      (Measure.pi (fun _ : H => Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin 3 => observationNoiseLaw))))
      (Measure.pi (fun _ : H × (Fin n × Fin 3) => observationNoiseLaw)) := by
  refine ⟨(flattenIndexedNoise n H).measurable,?_⟩
  refine (Measure.pi_eq (fun v hv => ?_)).symm
  rw [MeasurableEquiv.map_apply]
  have he : (flattenIndexedNoise n H) ⁻¹' Set.univ.pi v=
      Set.univ.pi (fun j => Set.univ.pi (fun i => Set.univ.pi (fun a => v (j,i,a)))) := by
    ext u
    simp only [mem_preimage,Set.mem_pi,mem_univ,true_implies,flattenIndexedNoise,
      MeasurableEquiv.coe_mk,Equiv.coe_fn_mk]
    exact ⟨fun h j i a => h (j,i,a),fun h ⟨j,i,a⟩ => h j i a⟩
  rw [he]
  simp only [Measure.pi_pi,Fintype.prod_prod_type]

lemma retainedNoise_preserving (n J j : ℕ) :
    MeasurePreserving (@retainedNoise n J j) (allObservationNoiseLaw n J)
      (Measure.pi (fun _ : RetainedScales J j × (Fin n × Fin 3) => observationNoiseLaw)) := by
  have hp : MeasurePreserving
      (fun u : ObservationNoise n J => fun k : RetainedScales J j => u k.val)
      (allObservationNoiseLaw n J)
      (Measure.pi (fun _ : RetainedScales J j =>
        Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin 3 => observationNoiseLaw)))) :=
    measurePreserving_fst.comp (measurePreserving_piEquivPiSubtypeProd
      (fun _ : Fin J => Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin 3 => observationNoiseLaw)))
      (fun k : Fin J => j≤k.val))
  exact (flattenIndexedNoise_preserving n (RetainedScales J j)).comp hp

lemma measurable_retainedObservationData {n J : ℕ} (j : ℕ) (ℓ : RetainedScales J j → ℝ) :
    Measurable (@retainedObservationData n J j ℓ) := by
  unfold retainedObservationData
  fun_prop

lemma arrayEventLikelihood_retained_integral {n J : ℕ} (j : ℕ) (ℓ : RetainedScales J j → ℝ)
    (hℓ : ∀ h, ℓ h≠0) (B : Set ((RetainedScales J j × (Fin n × Fin 3)) → ℝ))
    (hB : MeasurableSet B) (x : Configuration n) :
    arrayEventLikelihood ℓ B x=
      ∫ u, B.indicator (fun _ => (1:ℝ)) (retainedObservationData j ℓ (x,u))
        ∂allObservationNoiseLaw n J := by
  have hm : Measurable (fun u : (RetainedScales J j × (Fin n × Fin 3)) → ℝ =>
      B.indicator (fun _ => (1:ℝ)) (fun ia => x ia.2.1 ia.2.2+ℓ ia.1*u ia)) :=
    (measurable_const.indicator hB).comp (by fun_prop)
  rw [arrayEventLikelihood_integral ℓ hℓ,←(retainedNoise_preserving n J j).map_eq]
  exact integral_map_of_stronglyMeasurable (retainedNoise_preserving n J j).measurable hm.stronglyMeasurable

theorem physical_retainedEvent_bayes_integral {n J : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hn : normSquared ψ=1)
    (j : ℕ) (ℓ : RetainedScales J j → ℝ) (hℓ : ∀ k, ℓ k≠0)
    {B : Set ((RetainedScales J j × (Fin n × Fin 3)) → ℝ)} (hB : MeasurableSet B)
    {F : Configuration n → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ x, ‖F x‖≤C) :
    (∫ sample, (retainedObservationData j ℓ ⁻¹' B).indicator (fun z => F z.1) sample
      ∂observationLaw J (rawLaw ψ))=
    stateWeightedIntegral ψ (fun x => arrayEventLikelihood ℓ B x*F x) := by
  let := rawLaw_isProbability hψ hn
  have hi : Integrable (fun z : ObservationSample n J => F z.1)
      (observationLaw J (rawLaw ψ)) :=
    (integrable_const C).mono' (hF.comp measurable_fst).aestronglyMeasurable
      (Eventually.of_forall (fun z => hC z.1))
  have hA := hB.preimage (measurable_retainedObservationData j ℓ)
  rw [observationLaw,integral_prod _ (hi.indicator hA)]
  have hi2 : (fun x : Configuration n => ∫ u,
      (retainedObservationData j ℓ ⁻¹' B).indicator (fun z => F z.1) (x,u)
        ∂allObservationNoiseLaw n J)=
      fun x => arrayEventLikelihood ℓ B x*F x := by
    funext x
    rw [arrayEventLikelihood_retained_integral j ℓ hℓ B hB x,←integral_mul_const]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by
      by_cases h : retainedObservationData j ℓ (x,u)∈B <;> simp [h]
  rw [hi2,integral_rawLaw hψ]
  apply rawExpectation_eq_stateWeightedIntegral (C:=C) hψ
    (((arrayEventLikelihood_contDiff ℓ hB).continuous.measurable).mul hF)
  intro x
  change ‖arrayEventLikelihood ℓ B x*F x‖≤C
  rw [norm_mul,Real.norm_of_nonneg (arrayEventLikelihood_nonneg ℓ hB x)]
  exact (mul_le_mul_of_nonneg_right (arrayEventLikelihood_le_one ℓ hB x)
    (norm_nonneg _)).trans (by simpa using hC x)
end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace NeutralAtom

lemma measurable_retainedTailObservation {n J : ℕ} (j : ℕ) :
    Measurable (@retainedTailObservation n J j) := by
  apply Measurable.of_eval
  intro k
  by_cases hk : j≤k.val
  · simpa only [retainedTailObservation,dite_eq_left hk,Function.comp_def] using
      measurable_forgetOrder.comp (measurable_observationArrayPositions (⟨k,hk⟩ : RetainedScales J j))
  · simpa only [retainedTailObservation,dite_eq_right hk] using
      (measurable_const : Measurable (fun _ : (RetainedScales J j × (Fin n × Fin 3)) → ℝ =>
        forgetOrder (0 : Configuration n)))

lemma retainedTailObservation_permute {n J : ℕ} (j : ℕ)
    (p : Equiv.Perm (Fin n)) (z : (RetainedScales J j × (Fin n × Fin 3)) → ℝ) :
    retainedTailObservation j (permuteObservationArray p z)=retainedTailObservation j z := by
  funext k
  by_cases hk : j≤k.val
  · simp only [retainedTailObservation,dite_eq_left hk]
    exact forgetOrder_permutation (observationArrayPositions ⟨k,hk⟩ z) p
  · simp only [retainedTailObservation,dite_eq_right hk]

lemma retainedTailObservation_physical {n J : ℕ} (r : Fin J → ℝ)
    (j : ℕ) (sample : ObservationSample n J) :
    retainedTailObservation j (retainedObservationData j (fun k => (r k.val)^(101/100:ℝ)) sample)=
      tailObservation r j sample := by
  funext k
  by_cases hk : j≤k.val
  · simp only [retainedTailObservation,tailObservation,dite_eq_left hk,ite_eq_left hk,observedArray]
    congr 1
    funext i
    ext a
    simp [observationArrayPositions,retainedObservationData,observedOrdered,
      observationNoiseVector_coordinate]
  · simp only [retainedTailObservation,tailObservation,dite_eq_right hk,ite_eq_right hk]

lemma physical_retainedTailEvent_bayes_integral {n J : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hn : normSquared ψ=1)
    (r : Fin J → ℝ) (hr : ∀ k, 0 < r k) (j : ℕ)
    {B : Set (Fin J → UnorderedArray n)} (hB : MeasurableSet B)
    {F : Configuration n → ℝ} (hF : Measurable F) {C : ℝ}
    (hC : ∀ x, ‖F x‖≤C) :
    (∫ sample, (tailObservation r j ⁻¹' B).indicator (fun z => F z.1) sample
      ∂observationLaw J (rawLaw ψ))=
    stateWeightedIntegral ψ (fun x =>
      arrayEventLikelihood (fun k : RetainedScales J j => (r k.val)^(101/100:ℝ))
        (retainedTailObservation j ⁻¹' B) x*F x) := by
  have he : retainedObservationData j (fun k => (r k.val)^(101/100:ℝ)) ⁻¹'
      (retainedTailObservation j ⁻¹' B)=tailObservation r j ⁻¹' B := by
    ext sample
    simp only [mem_preimage,retainedTailObservation_physical]
  rw [←he]
  exact physical_retainedEvent_bayes_integral hψ hn j _
    (fun k => (Real.rpow_pos_of_pos (hr k.val) _).ne')
    (hB.preimage (measurable_retainedTailObservation j)) hF hC

lemma physical_retainedTailEvent_probability {n J : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hn : normSquared ψ=1)
    (r : Fin J → ℝ) (hr : ∀ k, 0 < r k) (j : ℕ)
    {B : Set (Fin J → UnorderedArray n)} (hB : MeasurableSet B) :
    (observationLaw J (rawLaw ψ)).real (tailObservation r j ⁻¹' B)=
    stateWeightedIntegral ψ (arrayEventLikelihood (fun k : RetainedScales J j => (r k.val)^(101/100:ℝ))
      (retainedTailObservation j ⁻¹' B)) := by
  have H := physical_retainedTailEvent_bayes_integral hψ hn r hr j hB
    (measurable_const : Measurable (fun _ : Configuration n => (1:ℝ)))
    (C:=1) (fun _ => by simp)
  simpa only [integral_indicator_const _ (hB.preimage (measurable_tailObservation r j)),
    smul_eq_mul,mul_one] using H

end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_RetainedPotentialMean
attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace NeutralAtom

lemma fromH1_raw_bounded_integral {n : ℕ} (u : Coulomb.H1Vector n)
    {F : Configuration n → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ x, ‖F x‖≤C) :
    (∫ x,F x ∂rawLaw (fromH1Wave u))=
      Coulomb.potentialForm (fun x => F ((flattenConfiguration n).symm x)) u := by
  have hu (σ : Spins n) : MemLp (fromH1Wave u σ) 2 volume :=
    (u.value_L2 σ).comp_measurePreserving (flattenConfiguration_measurePreserving n)
  rw [integral_rawLaw hu,rawExpectation_eq_stateWeightedIntegral hu hF hC]
  unfold stateWeightedIntegral Coulomb.potentialForm
  apply Finset.sum_congr rfl
  intro σ _
  have H := (flattenConfiguration_measurePreserving n).integral_comp'
    (fun x => F ((flattenConfiguration n).symm x)*‖u.value σ x‖^2)
  change (∫ x : Configuration n, F ((flattenConfiguration n).symm (flattenConfiguration n x))*
    ‖fromH1Wave u σ x‖^2)=_ at H
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using H

theorem retainedEvent_potential_mean {n J : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hn : normSquared ψ=1)
    (r : Fin J → ℝ) (hr : ∀ k, 0 < r k) (j : ℕ)
    {B : Set (Fin J → UnorderedArray n)} (hB : MeasurableSet B)
    (u : Coulomb.H1Vector n) (hum : Coulomb.mass u=1)
    (hlaw : ∀ F : Coulomb.Configuration n → ℝ, Coulomb.potentialForm F u=
      (stateWeightedIntegral ψ (arrayEventLikelihood
        (fun k : RetainedScales J j => (r k.val)^(101/100:ℝ)) (retainedTailObservation j ⁻¹' B)))⁻¹*
      stateWeightedIntegral ψ (fun x => arrayEventLikelihood
        (fun k : RetainedScales J j => (r k.val)^(101/100:ℝ)) (retainedTailObservation j ⁻¹' B) x*
        F (flattenConfiguration n x)))
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g) (hm : (∫ z,g z^2)=1)
    {c r₀ s : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀) (hs : 0 < s) (y : Position) :
    letI := rawLaw_isProbability hψ hn
    potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y=
      ((observationLaw J (rawLaw ψ)).real (tailObservation r j ⁻¹' B))⁻¹*
        ∫ z in tailObservation r j ⁻¹' B,
          potentialOf (conditionalPacketDensity (observationLaw J (rawLaw ψ)) Prod.fst
            (tailObservation r j) g c r₀ s (tailObservation r j z)) y ∂observationLaw J (rawLaw ψ) := by
  let := rawLaw_isProbability hψ hn
  have hu (σ : Spins n) : MemLp (fromH1Wave u σ) 2 volume :=
    (u.value_L2 σ).comp_measurePreserving (flattenConfiguration_measurePreserving n)
  have := rawLaw_isProbability hu ((fromH1_mass u).trans hum)
  obtain ⟨C,hC,H⟩ := rawPacketPotential_uniform (n:=n) hg hgs hm hc hr₀ hs
  have hF := measurable_rawPacketPotential (n:=n) hg hc hr₀ hs y
  have hbound (x : Configuration n) : ‖potentialOf (rawPacketDensity g c r₀ s x) y‖≤C := by
    rw [Real.norm_of_nonneg (H x y).2.1]
    exact (H x y).2.2
  rw [mixturePacketPotential hg hgs hm hc hr₀ hs,fromH1_raw_bounded_integral u hF hbound,hlaw]
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  rw [←physical_retainedTailEvent_probability hψ hn r hr j hB,
    ←physical_retainedTailEvent_bayes_integral hψ hn r hr j hB hF hbound,
    integral_indicator (hB.preimage (measurable_tailObservation r j))]
  congr 1
  exact (physical_observation_potential_tower (rawLaw ψ) r j hg hgs hm hc hr₀ hs
    (show MeasurableSet[observationSigma r j] (tailObservation r j ⁻¹' B) from ⟨B,hB,rfl⟩) y).symm

lemma conditionalPacketPotential_integrable {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure (Configuration n)) [IsFiniteMeasure ν]
    {raw : Ω → Configuration n} {obs : Ω → B}
    (hraw : MeasurePreserving raw P ν) (hobs : Measurable obs)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g)
    (hm : (∫ z,g z^2)=1) {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s)
    (y : Position) :
    Integrable (fun sample => potentialOf (conditionalPacketDensity P raw obs g c r₀ s (obs sample)) y) P :=
  (integrable_condExp (f:=fun sample => potentialOf (rawPacketDensity g c r₀ s (raw sample)) y)).congr
    (conditionalPacketPotential_eq_condExp P ν hraw hobs hg hgs hm hc hr hs y).symm

lemma normalized_event_const_sub {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {A : Set Ω} {f : Ω → ℝ} (hi : Integrable f P)
    (hp : 0<P.real A) (C : ℝ) :
    (P.real A)⁻¹*(∫ x in A,C-f x ∂P)=C-(P.real A)⁻¹*(∫ x in A,f x ∂P) := by
  rw [integral_sub (integrable_const C) hi.integrableOn,integral_const]
  simp only [smul_eq_mul,measureReal_restrict_apply_univ]
  rw [mul_sub,←mul_assoc,inv_mul_cancel₀ hp.ne',one_mul]

lemma le_normalized_event {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {A : Set Ω} (hA : MeasurableSet A) {f : Ω → ℝ}
    (hi : Integrable f P) (hp : 0<P.real A) {v : ℝ}
    (hb : ∀ᵐ x ∂P, x∈A → v≤f x) :
    v≤(P.real A)⁻¹*(∫ x in A,f x ∂P) := by
  have h := setIntegral_mono_ae_restrict (integrable_const v) hi.integrableOn
    ((ae_restrict_iff' hA).mpr hb)
  rw [integral_const] at h
  simp only [smul_eq_mul,measureReal_restrict_apply_univ] at h
  have hh := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hp.le)
  simpa only [←mul_assoc,inv_mul_cancel₀ hp.ne',one_mul] using hh

theorem retainedEvent_field_mean {n J : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hn : normSquared ψ=1)
    (r : Fin J → ℝ) (hr : ∀ k, 0 < r k) (j : ℕ)
    {B : Set (Fin J → UnorderedArray n)} (hB : MeasurableSet B)
    (u : Coulomb.H1Vector n) (hum : Coulomb.mass u=1)
    (hlaw : ∀ F : Coulomb.Configuration n → ℝ, Coulomb.potentialForm F u=
      (stateWeightedIntegral ψ (arrayEventLikelihood
        (fun k : RetainedScales J j => (r k.val)^(101/100:ℝ)) (retainedTailObservation j ⁻¹' B)))⁻¹*
      stateWeightedIntegral ψ (fun x => arrayEventLikelihood
        (fun k : RetainedScales J j => (r k.val)^(101/100:ℝ)) (retainedTailObservation j ⁻¹' B) x*
        F (flattenConfiguration n x)))
    (hp : 0<(observationLaw J (rawLaw ψ)).real (tailObservation r j ⁻¹' B))
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g) (hm : (∫ z,g z^2)=1)
    {c r₀ s : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀) (hs : 0 < s) (y : Position) (V : ℝ) :
    letI := rawLaw_isProbability hψ hn
    V-potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y=
      ((observationLaw J (rawLaw ψ)).real (tailObservation r j ⁻¹' B))⁻¹*
        ∫ z in tailObservation r j ⁻¹' B,
          V-potentialOf (conditionalPacketDensity (observationLaw J (rawLaw ψ)) Prod.fst
            (tailObservation r j) g c r₀ s (tailObservation r j z)) y ∂observationLaw J (rawLaw ψ) := by
  let := rawLaw_isProbability hψ hn
  rw [normalized_event_const_sub
    (conditionalPacketPotential_integrable (observationLaw J (rawLaw ψ)) (rawLaw ψ)
      (observationLaw_rawProjection _) (measurable_tailObservation r j) hg hgs hm hc hr₀ hs y) hp]
  rw [retainedEvent_potential_mean hψ hn r hr j hB u hum hlaw hg hgs hm hc hr₀ hs y]

end NeutralAtom

end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_MasterNewton
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
noncomputable section
namespace NeutralAtom

lemma fixed_scaled_window_mass (g : 𝓢(Position,ℝ)) (hm : (∫ w,g w^2)=1)
    {t : ℝ} (ht : 0<t) : (∫ w : Position,(t^3)⁻¹*g (t⁻¹ • w)^2)=1 := by
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume (fun w : Position => g w^2) ht.le]
  simp only [Position,finrank_euclideanSpace_fin,smul_eq_mul,hm,mul_one]
  exact inv_mul_cancel₀ (pow_ne_zero _ ht.ne')

lemma fixed_scaled_window_integrable (g : 𝓢(Position,ℝ)) (hm : (∫ w,g w^2)=1)
    {t : ℝ} (ht : 0<t) : Integrable (fun w : Position => (t^3)⁻¹*g (t⁻¹ • w)^2) := by
  by_contra hn
  have hh := integral_undef hn
  rw [fixed_scaled_window_mass g hm ht] at hh
  exact one_ne_zero hh

lemma packet_potential_center_shift (g : Position → ℝ) (c r₀ s : ℝ) (z y : Position) :
    potentialOf (packetKernel g c r₀ s z) y =
      ∫ w, Coulomb.coulombKernel ((y-z)-w)*
        ((packetWidth c r₀ s z^3)⁻¹*g ((packetWidth c r₀ s z)⁻¹ • w)^2) := by
  rw [←integral_sub_right_eq_self (fun w : Position => Coulomb.coulombKernel ((y-z)-w)*
    ((packetWidth c r₀ s z^3)⁻¹*g ((packetWidth c r₀ s z)⁻¹ • w)^2)) z]
  unfold potentialOf packetKernel
  apply integral_congr_ae
  exact Eventually.of_forall fun w => by
    dsimp only
    rw [show (y-z)-(w-z)=y-w by abel]
    rfl

theorem packet_potential_newton_eq (g : 𝓢(Position,ℝ)) (hm : (∫ w,g w^2)=1)
    (hrad : ∀ w,g w=g (EuclideanSpace.single 0 ‖w‖))
    (hgs : ∀ w,1<‖w‖ → g w=0)
    {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s)
    {z y : Position} (hsep : packetWidth c r₀ s z≤‖y-z‖) :
    potentialOf (packetKernel g c r₀ s z) y=coulombKernel (y-z) := by
  let t := packetWidth c r₀ s z
  have ht : 0<t := packetWidth_pos hc hr hs z
  have hp (w : Position) : 0≤(t^3)⁻¹*g (t⁻¹ • w)^2 := by positivity
  have hb (w : Position) : (t^3)⁻¹*g (t⁻¹ • w)^2≤(t^3)⁻¹*(SchwartzMap.seminorm ℝ 0 0 g)^2 :=
    mul_le_mul_of_nonneg_left (Coulomb.schwartz_square_le g _) (by positivity)
  have hfr (w : Position) : (t^3)⁻¹*g (t⁻¹ • w)^2=
      (t^3)⁻¹*g (t⁻¹ • EuclideanSpace.single 0 ‖w‖)^2 := by
    have hh : ‖t⁻¹ • w‖=‖t⁻¹ • EuclideanSpace.single (0:Fin 3) ‖w‖‖ := by
      simp only [norm_smul,PiLp.norm_single,Real.norm_eq_abs,abs_norm]
    rw [hrad (t⁻¹ • w),hrad (t⁻¹ • EuclideanSpace.single 0 ‖w‖),hh]
  have hfs (w : Position) (hw : t<‖w‖) : (t^3)⁻¹*g (t⁻¹ • w)^2=0 := by
    have hn : 1<‖t⁻¹ • w‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht)]
      have hh := (lt_div_iff₀ ht).mpr (by simpa using hw : 1*t<‖w‖)
      simpa only [div_eq_mul_inv,mul_comm] using hh
    simp [hgs _ hn]
  rw [packet_potential_center_shift]
  have hx : y-z≠0 := by intro h; rw [h,norm_zero] at hsep; exact (not_le_of_gt ht) hsep
  have H := Coulomb.radial_coulomb_integral_eq (fixed_scaled_window_integrable g hm ht)
    (by fun_prop) hp hb hfr ht.le hfs hx hsep
  rw [fixed_scaled_window_mass g hm ht,mul_one] at H
  exact H

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_RawMasterNewton
attribute [-instance] _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
noncomputable section
namespace NeutralAtom

lemma integrable_packet_coulomb (g : 𝓢(Position,ℝ)) (hm : (∫ w,g w^2)=1)
    {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s) (z y : Position) :
    Integrable (fun w => coulombKernel (y-w)*packetKernel g c r₀ s z w) := by
  apply Coulomb.coulomb_convolution_integrable (integrable_packetKernel g hm hc hr hs z)
    (((continuous_packetKernel g.continuous hc hr hs).comp (continuous_const.prodMk continuous_id)).measurable)
    (packetKernel_nonneg g hc hr hs z)
    (M := (packetWidth c r₀ s z^3)⁻¹*(SchwartzMap.seminorm ℝ 0 0 g)^2)
    (fun w => mul_le_mul_of_nonneg_left (Coulomb.schwartz_square_le g _)
      (by have ht := packetWidth_pos hc hr hs z; positivity)) (by norm_num : (0:ℝ)<1) y

lemma rawPacketPotential_sum {n : ℕ} (g : 𝓢(Position,ℝ)) (hm : (∫ w,g w^2)=1)
    {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s)
    (x : Configuration n) (y : Position) :
    potentialOf (rawPacketDensity g c r₀ s x) y=∑ i : Fin n,potentialOf (packetKernel g c r₀ s (x i)) y := by
  unfold potentialOf rawPacketDensity
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum _ (fun i _ => integrable_packet_coulomb g hm hc hr hs (x i) y)

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_MasterTruncatedCap
attribute [-instance] _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap
noncomputable section
namespace NeutralAtom

lemma rawPacketPotential_ge_far {n : ℕ} (g : 𝓢(Position,ℝ)) (hm : (∫ z,g z^2)=1)
    (hrad : ∀ z,g z=g (EuclideanSpace.single 0 ‖z‖)) (hgs : ∀ z,1 < ‖z‖ → g z=0)
    {c r₀ s R : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀) (hs : 0 < s)
    (hscale : c*(1+packetExponent)*s^packetExponent ≤ 1/2)
    (y : Position) (hR : 2*packetWidth c r₀ s y ≤ R) (x : Configuration n) :
    Coulomb.restrictedOutPotential (flattenConfiguration n x) {z | R ≤ ‖z-y‖} y ≤
      potentialOf (rawPacketDensity g c r₀ s x) y := by
  rw [rawPacketPotential_sum g hm hc hr₀ hs]
  apply Finset.sum_le_sum
  intro i hi
  change (if R ≤ ‖x i-y‖ then ‖x i-y‖⁻¹ else 0) ≤ _
  split_ifs with h
  · have hl := packetWidth_lipschitz hc.le hr₀ hs (x i) y
    have H := mul_le_mul_of_nonneg_right hscale (norm_nonneg (x i-y))
    have hsep : packetWidth c r₀ s (x i) ≤ ‖y-x i‖ := by
      rw [norm_sub_rev]
      have H' := (le_abs_self (packetWidth c r₀ s (x i)-packetWidth c r₀ s y)).trans hl
      linarith
    rw [packet_potential_newton_eq g hm hrad hgs hc hr₀ hs hsep]
    simp only [coulombKernel,norm_sub_rev]
    exact le_rfl
  · exact integral_nonneg (fun z => mul_nonneg (coulombKernel_nonneg _)
      (packetKernel_nonneg g hc hr₀ hs (x i) z))

theorem master_field_le_truncated {n : ℕ} (u : Coulomb.H1Vector n) (hum : Coulomb.mass u=1)
    (g : 𝓢(Position,ℝ)) (hm : (∫ z,g z^2)=1)
    (hrad : ∀ z,g z=g (EuclideanSpace.single 0 ‖z‖)) (hgs : ∀ z,1 < ‖z‖ → g z=0)
    {c r₀ s R : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀) (hs : 0 < s) (hR : 0 < R)
    (hscale : c*(1+packetExponent)*s^packetExponent ≤ 1/2)
    (y : Position) (hwidth : 2*packetWidth c r₀ s y ≤ R) (V : ℝ) :
    V-potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y ≤
      V-Coulomb.restrictedCorePotential u {z | R ≤ ‖z-y‖} y := by
  have hu (σ : Spins n) : MemLp (fromH1Wave u σ) 2 volume :=
    (u.value_L2 σ).comp_measurePreserving (flattenConfiguration_measurePreserving n)
  have := rawLaw_isProbability hu ((fromH1_mass u).trans hum)
  have hgc : HasCompactSupport (g : Position → ℝ) :=
    HasCompactSupport.intro (isCompact_closedBall (0:Position) 1) (fun z hz =>
      hgs z (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz))
  let W := Coulomb.rawSignedField (n:=n) V {z | R ≤ ‖z-y‖} y
  have hA : MeasurableSet {z : Position | R ≤ ‖z-y‖} := measurableSet_le measurable_const (by fun_prop)
  have hW : Measurable W := Coulomb.rawSignedField_measurable _ hA y
  have hF := hW.comp (flattenConfiguration n).continuous.measurable
  have hB (x : Configuration n) : ‖W (flattenConfiguration n x)‖ ≤ |V|+(n:ℝ)/R := by
    exact Coulomb.rawSignedField_abs_le V _ y hR (fun _ hz => hz) _
  have hi : Integrable (fun x => W (flattenConfiguration n x)) (rawLaw (fromH1Wave u)) := Integrable.of_bound hF.aestronglyMeasurable (|V|+(n:ℝ)/R)
    (Eventually.of_forall hB)
  have hp := integrable_rawPacketPotential g.continuous hgc hm hc hr₀ hs (rawLaw (fromH1Wave u)) y
  have H := integral_mono (integrable_const V |>.sub hp) hi
    (fun x => sub_le_sub_left (rawPacketPotential_ge_far g hm hrad hgs hc hr₀ hs hscale y hwidth x) V)
  simp only [Pi.sub_apply] at H
  rw [integral_sub (integrable_const V) hp,integral_const,probReal_univ,smul_eq_mul,one_mul,
    ←mixturePacketPotential g.continuous hgc hm hc hr₀ hs] at H
  rw [fromH1_raw_bounded_integral u (F:=fun x => W (flattenConfiguration n x)) hF hB] at H
  simp only [ContinuousLinearEquiv.apply_symm_apply] at H
  rw [Coulomb.potentialForm_rawSignedField u V hA y hR (fun _ hz => hz),hum,mul_one] at H
  exact H

theorem atomic_master_field_cap {J n : ℕ} (S : Coulomb.Nuclei J)
    (hatom : ∀ i,S.position i=0) (u : Coulomb.H1Vector n)
    (hu : Coulomb.Antisymmetric u) (hum : Coulomb.mass u=1)
    {E δ : ℝ} (hE : (E:EReal) ≤ Coulomb.unrestrictedFormBottom S)
    (he : Coulomb.form S u ≤ E+δ) (hδ : 0 ≤ δ)
    (g : 𝓢(Position,ℝ)) (hm : (∫ z,g z^2)=1)
    (hrad : ∀ z,g z=g (EuclideanSpace.single 0 ‖z‖)) (hgs : ∀ z,1 < ‖z‖ → g z=0)
    {c r₀ s : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀) (hs : 0 < s)
    (hscale : c*(1+packetExponent)*s^packetExponent ≤ 1/2)
    (y : Position) (hy : y≠0) (hwidth : 2*packetWidth c r₀ s y ≤ 40*Coulomb.atomicCellScale y) :
    Coulomb.attraction S y-potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y ≤
      2*Coulomb.atomicBudgetRecursionC^2*
        Coulomb.screenFieldUnit δ Coulomb.atomicCountConstant (Coulomb.atomicCellScale y) := by
  have ha := Coulomb.atomicCellScale_pos hy
  exact (master_field_le_truncated u hum g hm hrad hgs hc hr₀ hs (by positivity)
    hscale y hwidth (Coulomb.attraction S y)).trans
    ((le_max_left _ _).trans (Coulomb.atomic_expected_raw_field_bound S hatom u hu hum hE he hδ hy))
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ObservationDyadicWidth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Filter
open scoped BigOperators Topology Classical
namespace NeutralAtom

lemma observationWidthSquareSum_retained_dyadic {r : ℝ} (hr : 0 < r) (J j : ℕ) :
    observationWidthSquareSum (fun k : RetainedScales J j =>
      (r*2^k.val.val)^(101/100:ℝ))≤
      (4/3:ℝ)*(((r*2^j)^(101/100:ℝ))⁻¹)^2 := by
  let sh : RetainedScales J j → Fin J :=
    fun k => ⟨k.val.val-j, lt_of_le_of_lt (Nat.sub_le _ _) k.val.isLt⟩
  have hs : Function.Injective sh := by
    intro k l h
    apply Subtype.ext
    apply Fin.ext
    have he := congrArg Fin.val h
    dsimp [sh] at he
    have hk := k.property
    have hl := l.property
    omega
  have hg : (∑ k : RetainedScales J j, (1/4:ℝ)^(k.val.val-j))≤4/3 := by
    calc
      _ = ∑ k ∈ Finset.univ.image sh, (1/4:ℝ)^k.val := by
        rw [Finset.sum_image (by intro a _ b _ hab; exact hs hab)]
      _ ≤ ∑ k : Fin J, (1/4:ℝ)^k.val :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => by positivity)
      _ ≤ 4/3 := by
        rw [Fin.sum_univ_eq_sum_range]
        have H := geom_sum_mul_neg (1/4:ℝ) J
        have hn := pow_nonneg (by norm_num : (0:ℝ)≤1/4) J
        nlinarith
  have hp := Real.rpow_pos_of_pos (by positivity : 0 < r*2^j) (101/100:ℝ)
  unfold observationWidthSquareSum
  calc
    _ ≤ ∑ k : RetainedScales J j,
        (((r*2^j)^(101/100:ℝ))⁻¹)^2*(1/4:ℝ)^(k.val.val-j) := by
      apply Finset.sum_le_sum
      intro k _
      have heq : r*2^j*2^(k.val.val-j)=r*2^k.val.val := by
        rw [mul_assoc,←pow_add,Nat.add_sub_of_le k.property]
      have hpow : (2:ℝ)^(k.val.val-j)≤((2:ℝ)^(k.val.val-j))^(101/100:ℝ) :=
        Real.self_le_rpow_of_one_le (one_le_pow₀ (by norm_num)) (by norm_num)
      have hfactor : (r*2^k.val.val)^(101/100:ℝ)=
          (r*2^j)^(101/100:ℝ)*((2:ℝ)^(k.val.val-j))^(101/100:ℝ) := by
        rw [←heq]
        exact Real.mul_rpow (by positivity) (by positivity)
      have hwidth : (r*2^j)^(101/100:ℝ)*2^(k.val.val-j)≤(r*2^k.val.val)^(101/100:ℝ) := by
        rw [hfactor]
        exact mul_le_mul_of_nonneg_left hpow hp.le
      have hi : ((r*2^k.val.val)^(101/100:ℝ))⁻¹≤
          ((r*2^j)^(101/100:ℝ)*2^(k.val.val-j))⁻¹ :=
        (inv_le_inv₀ (Real.rpow_pos_of_pos (by positivity) _) (by positivity)).2 hwidth
      convert pow_le_pow_left₀ (inv_nonneg.mpr (Real.rpow_nonneg (by positivity) _)) hi 2 using 1
      all_goals try with_reducible_and_instances rfl
      have he : ((2:ℝ)^(k.val.val-j))⁻¹^2=(1/4:ℝ)^(k.val.val-j) := by
        rw [←inv_pow,←pow_mul,Nat.mul_comm (k.val.val-j) 2,pow_mul,inv_pow]
        norm_num
      rw [mul_inv_rev,mul_pow,he]
      ring
    _ = (((r*2^j)^(101/100:ℝ))⁻¹)^2*(∑ k : RetainedScales J j, (1/4:ℝ)^(k.val.val-j)) := by
      rw [Finset.mul_sum]
    _ ≤ (((r*2^j)^(101/100:ℝ))⁻¹)^2*(4/3:ℝ) :=
      mul_le_mul_of_nonneg_left hg (sq_nonneg _)
    _ = _ := mul_comm _ _
end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PosteriorDataMeasurable
attribute [-instance] _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap
namespace NeutralAtom

lemma measurable_conditionalPacketPotential_data {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (raw : Ω → Configuration n) (obs : Ω → B)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g)
    (hm : (∫ z,g z^2)=1) {c r₀ s : ℝ}
    (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s) (y : Position) :
    Measurable (fun datum => potentialOf (conditionalPacketDensity P raw obs g c r₀ s datum) y) := by
  have H := ((measurable_rawPacketPotential (n:=n) hg hc hr hs y).stronglyMeasurable.integral_kernel
      (κ:=ProbabilityTheory.condDistrib raw obs P)).measurable
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext datum
  exact mixturePacketPotential hg hgs hm hc hr hs _ y

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PhysicalPosteriorInverse
attribute [-instance] _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
namespace NeutralAtom

lemma mixturePacketDensity_measurable {n : ℕ} (ν : Measure (Configuration n)) [SFinite ν]
    {g : Position → ℝ} (hg : Continuous g) {c r₀ s : ℝ}
    (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s) :
    Measurable (mixturePacketDensity ν g c r₀ s) :=
  (continuous_rawPacketDensity hg hc hr hs).stronglyMeasurable.integral_prod_left'.measurable

lemma conditionalPacketPotential_continuous {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (raw : Ω → Configuration n) (obs : Ω → B)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g)
    (hm : (∫ z,g z^2)=1) {c r₀ s : ℝ}
    (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s) (datum : B) :
    Continuous (potentialOf (conditionalPacketDensity P raw obs g c r₀ s datum)) := by
  obtain ⟨A,hA,HA⟩ := conditionalPacketDensity_bounded P raw obs hg hgs hc hr hs
  exact potentialOf_continuous (mixturePacketDensity_integrable hg hm hc hr hs _)
    (conditionalPacketDensity_nonneg P raw obs g hc hr hs datum) (HA datum)

lemma measurable_conditionalPacketPotential_joint {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (raw : Ω → Configuration n) (obs : Ω → B)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g)
    (hm : (∫ z,g z^2)=1) {c r₀ s : ℝ}
    (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s) :
    Measurable (fun dy : B × Position => potentialOf
      (conditionalPacketDensity P raw obs g c r₀ s dy.1) dy.2) := by
  let u := fun y : Position => fun datum : B => potentialOf
    (conditionalPacketDensity P raw obs g c r₀ s datum) y
  have hcont : ∀ datum, Continuous (fun y => u y datum) :=
    conditionalPacketPotential_continuous P raw obs hg hgs hm hc hr hs
  have hmeas : ∀ y, Measurable (u y) :=
    measurable_conditionalPacketPotential_data P raw obs hg hgs hm hc hr hs
  have H : Measurable (Function.uncurry u) :=
    measurable_uncurry_of_continuous_of_measurable hcont hmeas
  change Measurable (Function.uncurry u ∘ (Prod.swap : B × Position → Position × B))
  exact Measurable.comp H measurable_swap

lemma atomic_screened_ballCloud_submean {ρ : Position → ℝ} (hi : Integrable ρ)
    (hm : Measurable ρ) (hp : ∀ x,0≤ρ x) {A : ℝ} (hA : ∀ x,ρ x≤A)
    (Z : ℝ) {a : ℝ} (ha : 0<a) (y : Position) (hy : a≤‖y‖) :
    Z*coulombKernel y-potentialOf ρ y ≤ ∫ z,
      (Z*coulombKernel z-potentialOf ρ z)*Coulomb.ballCloud y a 1 z := by
  have hnI : Integrable (fun z => coulombKernel z*Coulomb.ballCloud y a 1 z) := by
    have H := Coulomb.coulomb_convolution_integrable (Coulomb.ballCloud_integrable a 1 y)
      (Coulomb.ballCloud_measurable a 1 y) (fun z => Coulomb.uniformBall_nonneg ha zero_le_one (z-y))
      (fun z => Coulomb.uniformBall_le ha zero_le_one (z-y)) ha (0:Position)
    simpa only [Coulomb.coulombKernel,coulombKernel,zero_sub,norm_neg] using H
  have he : (∫ z,coulombKernel z*Coulomb.ballCloud y a 1 z)=coulombKernel y := by
    have H := Coulomb.ballCloud_coulomb ha zero_le_one y (0:Position) (by simpa only [zero_sub,norm_neg] using hy)
    simpa only [Coulomb.coulombKernel,coulombKernel,zero_sub,norm_neg,one_mul] using H
  have hK := Coulomb.coulomb_convolution_integrable hi hm hp hA (by norm_num : (0:ℝ)<1) y
  have H := Coulomb.potentialOf_ballCloud_le hi hm hp ha y hK
  simp_rw [sub_mul,mul_assoc]
  rw [integral_sub (hnI.const_mul Z) (Coulomb.potentialOf_ballCloud_integrable hi hm ha y),
    integral_const_mul,he]
  linarith

lemma conditionalPacketField_submean {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (raw : Ω → Configuration n) (obs : Ω → B)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g)
    (hm : (∫ z,g z^2)=1) {c r₀ s : ℝ}
    (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s) (datum : B)
    (Z : ℝ) {a : ℝ} (ha : 0<a) (y : Position) (hy : a≤‖y‖) :
    Z*coulombKernel y-potentialOf (conditionalPacketDensity P raw obs g c r₀ s datum) y ≤
      (4*Real.pi/3*a^3)⁻¹*∫ z in Metric.closedBall y a,
      Z*coulombKernel z-potentialOf (conditionalPacketDensity P raw obs g c r₀ s datum) z := by
  let ρ := conditionalPacketDensity P raw obs g c r₀ s datum
  have hi : Integrable ρ := mixturePacketDensity_integrable hg hm hc hr hs _
  have hρm : Measurable ρ := mixturePacketDensity_measurable _ hg hc hr hs
  obtain ⟨A,hA,HA⟩ := conditionalPacketDensity_bounded P raw obs hg hgs hc hr hs
  have hp : ∀ x,0≤ρ x := conditionalPacketDensity_nonneg P raw obs g hc hr hs datum
  have H := atomic_screened_ballCloud_submean hi hρm hp (HA datum) Z ha y hy
  rw [Coulomb.integral_ballCloud] at H
  exact H
end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_AnnularSubmeanCap
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace NeutralAtom

lemma cap_ball_geometry {r L : ℝ} (hr : 0 < r) (hL : 1≤L) {y z : Position}
    (hy0 : 3*r/4≤‖y‖) (hy1 : ‖y‖≤6*L*r)
    (hz : z∈Metric.closedBall y (r/8)) :
    r/2≤‖z‖ ∧ ‖z‖≤8*L*r ∧ ‖y‖≤2*‖z‖ := by
  have hd : ‖z-y‖ ≤ r/8 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
  have h1 : ‖y‖≤‖z‖+‖z-y‖ := by
    simpa only [add_sub_cancel, norm_sub_rev] using norm_add_le z (y-z)
  have h2 : ‖z‖≤‖y‖+‖z-y‖ := by
    simpa only [add_sub_cancel] using norm_add_le y (z-y)
  have hLr : r≤L*r := by nlinarith
  constructor
  · linarith
  constructor <;> linarith

lemma annular_submean_cap {F : Position → ℝ} {r L T : ℝ}
    (hr : 0 < r) (hL : 1≤L) (hT : 0≤T)
    (hE : IntegrableOn (fun z => max (‖z‖^4*F z-T) 0)
      {z | r/2≤‖z‖ ∧ ‖z‖≤8*L*r}) {y : Position}
    (hy0 : 3*r/4≤‖y‖) (hy1 : ‖y‖≤6*L*r)
    (hF : IntegrableOn F (Metric.closedBall y (r/8)))
    (hmean : F y≤(4*Real.pi/3*(r/8)^3)⁻¹*(∫ z in Metric.closedBall y (r/8),F z)) :
    ‖y‖^4*F y≤16*T+16*(4*Real.pi/3*(r/8)^3)⁻¹*
      ∫ z in {z | r/2≤‖z‖ ∧ ‖z‖≤8*L*r},max (‖z‖^4*F z-T) 0 := by
  let A : Set Position := {z | r/2≤‖z‖ ∧ ‖z‖≤8*L*r}
  let B := Metric.closedBall y (r/8)
  let V := 4*Real.pi/3*(r/8)^3
  let E := fun z : Position => max (‖z‖^4*F z-T) 0
  have hV : 0<V := by dsimp [V]; positivity
  have hsub : B⊆A := fun z hz => (cap_ball_geometry hr hL hy0 hy1 hz).1 |> fun h0 =>
    ⟨h0,(cap_ball_geometry hr hL hy0 hy1 hz).2.1⟩
  have hEB : IntegrableOn E B := hE.mono_set hsub
  have hloc (z : Position) (hz : z∈B) : ‖y‖^4*F z≤16*T+16*E z := by
    have H := cap_ball_geometry hr hL hy0 hy1 hz
    have he : ‖z‖^4*F z≤T+E z := by dsimp [E]; linarith [le_max_left (‖z‖^4*F z-T) 0]
    by_cases hf : 0≤F z
    · have hn : ‖y‖^4≤16*‖z‖^4 := by
        have hh := pow_le_pow_left₀ (norm_nonneg y) H.2.2 4
        norm_num [mul_pow] at hh ⊢
        exact hh
      have hh := mul_le_mul_of_nonneg_right hn hf
      nlinarith
    · have hf' : F z≤0 := le_of_not_ge hf
      have hh := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (norm_nonneg y) 4) hf'
      have he0 : 0≤E z := le_max_right _ _
      linarith
  have hcI : IntegrableOn (fun _ : Position => (16*T:ℝ)) B :=
    integrableOn_const (isCompact_closedBall y (r/8)).measure_ne_top
  have hIB : (∫ z in B,‖y‖^4*F z)≤∫ z in B,16*T+16*E z := by
    apply setIntegral_mono_on (hF.const_mul _) (hcI.add (hEB.const_mul _))
      measurableSet_closedBall
    exact hloc
  have hIE : (∫ z in B,E z)≤∫ z in A,E z := by
    apply setIntegral_mono_set hE
    · exact Eventually.of_forall (fun z => le_max_right _ _)
    · exact Eventually.of_forall (fun _ hz => hsub hz)
  have hconst : (∫ z in B,(16*T:ℝ))=V*(16*T) := by
    rw [integral_const,smul_eq_mul,measureReal_restrict_apply_univ]
    rw [show volume.real B=V from Coulomb.volume_closedBall_three _ (by positivity)]
  rw [integral_const_mul,integral_add hcI (hEB.const_mul _),
    hconst,integral_const_mul] at hIB
  have hm := mul_le_mul_of_nonneg_left hmean (pow_nonneg (norm_nonneg y) 4)
  have hIB' := mul_le_mul_of_nonneg_left hIB (inv_nonneg.mpr hV.le)
  have hIV : V⁻¹*V=1 := inv_mul_cancel₀ hV.ne'
  change ‖y‖^4*F y≤16*T+16*V⁻¹*∫ z in A,E z
  calc
    _ ≤ V⁻¹*(‖y‖^4*(∫ z in B,F z)) := by simpa only [V,B,mul_left_comm] using hm
    _ ≤ V⁻¹*(V*(16*T)+16*(∫ z in B,E z)) := hIB'
    _ = 16*T+16*V⁻¹*(∫ z in B,E z) := by rw [mul_add,←mul_assoc,hIV]; ring
    _ ≤ _ := by linarith [mul_le_mul_of_nonneg_left hIE (show 0≤16*V⁻¹ by positivity)]
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace NeutralAtom

lemma spatial_moment_markov {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {A : Set Position}
    (hA : MeasurableSet A) (hAfin : volume A<∞)
    {Q : Ω × Position → ℝ} (hQ : Measurable Q) (hQ0 : ∀ z,0≤Q z)
    {B M : ℝ} (hB : ∀ ω y,y∈A → Q (ω,y)≤B)
    (hM : ∀ y,y∈A → (∫ ω,Q (ω,y) ∂P)≤M) {t : ℝ} (ht : 0<t) :
    Measurable (fun ω => ∫ y in A,Q (ω,y)) ∧
    (∀ ω,IntegrableOn (fun y => Q (ω,y)) A) ∧
    P.real {ω | t<(∫ y in A,Q (ω,y))}≤volume.real A*M/t := by
  have : IsFiniteMeasure (volume.restrict A) := ⟨by simpa only [Measure.restrict_apply_univ] using hAfin⟩
  have hI (ω : Ω) : IntegrableOn (fun y => Q (ω,y)) A := by
    apply Integrable.of_bound ((hQ.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable) B
    filter_upwards [ae_restrict_mem hA] with y hy
    change ‖Q (ω,y)‖≤B
    rw [Real.norm_of_nonneg (hQ0 _)]
    exact hB ω y hy
  have hprod : Integrable Q (P.prod (volume.restrict A)) := by
    apply Integrable.of_bound hQ.aestronglyMeasurable B
    rw [Measure.ae_prod_iff_ae_ae (measurableSet_le hQ.norm measurable_const)]
    filter_upwards [] with ω
    filter_upwards [ae_restrict_mem hA] with y hy
    rw [Real.norm_of_nonneg (hQ0 _)]
    exact hB ω y hy
  have hIm : Measurable (fun ω => ∫ y in A,Q (ω,y)) :=
    hQ.stronglyMeasurable.integral_prod_right'.measurable
  refine ⟨hIm,hI,?_⟩
  have hswap : (∫ ω,(∫ y in A,Q (ω,y)) ∂P)=(∫ y in A,∫ ω,Q (ω,y) ∂P) :=
    integral_integral_swap hprod
  have hmean : (∫ ω,(∫ y in A,Q (ω,y)) ∂P)≤volume.real A*M := by
    rw [hswap]
    calc
      _ ≤ ∫ y in A,M := integral_mono_ae hprod.integral_prod_right (integrable_const M)
        (by filter_upwards [ae_restrict_mem hA] with y hy; exact hM y hy)
      _ = _ := by simp only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul]
  have hMark := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun ω => integral_nonneg (fun y => hQ0 (ω,y))))
    hprod.integral_prod_left t
  have hprob : P.real {ω | t<(∫ y in A,Q (ω,y))}≤P.real {ω | t≤(∫ y in A,Q (ω,y))} :=
    measureReal_mono (by
      intro ω hω
      exact (show t<(∫ y in A,Q (ω,y)) from hω).le)
  apply (le_div_iff₀ ht).2
  have hh := mul_le_mul_of_nonneg_left hprob ht.le
  linarith
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_LogTailMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace NeutralAtom

lemma log_probability_fifth {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    (1-Real.log p)^5 ≤ 251^5*p^(-1/50:ℝ) := by
  have hlog : 0 ≤ 1-Real.log p := by linarith [Real.log_nonpos hp.le hp1]
  have h := Real.log_le_rpow_div (inv_nonneg.mpr hp.le) (by norm_num : (0:ℝ) < 1/250)
  rw [Real.log_inv,Real.inv_rpow hp.le,←Real.rpow_neg hp.le] at h
  have hpow : 1 ≤ p^(-1/250:ℝ) := by
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hp hp1 (by norm_num)
  have hlin : 1-Real.log p ≤ 251*p^(-1/250:ℝ) := by linarith
  have H := pow_le_pow_left₀ hlog hlin 5
  apply H.trans_eq
  rw [mul_pow]
  congr 1
  rw [←Real.rpow_natCast,←Real.rpow_mul hp.le]
  norm_num

lemma probability_of_log_fifth {p b d : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hb : 0 < b) (hd : 0 ≤ d)
    (h : b^2 ≤ d*(1-Real.log p)^5) :
    p ≤ (251^5*d)^50/b^100 := by
  have H := h.trans (mul_le_mul_of_nonneg_left (log_probability_fifth hp hp1) hd)
  have hpw : 0 < p^(1/50:ℝ) := Real.rpow_pos_of_pos hp _
  have H' := mul_le_mul_of_nonneg_right H hpw.le
  have he : p^(-1/50:ℝ)*p^(1/50:ℝ)=1 := by
    rw [←Real.rpow_add hp]; norm_num
  have HH : b^2*p^(1/50:ℝ) ≤ 251^5*d := by
    calc
      _ ≤ d*(251^5*p^(-1/50:ℝ))*p^(1/50:ℝ) := H'
      _ = (251^5*d)*(p^(-1/50:ℝ)*p^(1/50:ℝ)) := by ring
      _ = _ := by rw [he,mul_one]
  have Hpow := pow_le_pow_left₀ (by positivity : 0 ≤ b^2*p^(1/50:ℝ)) HH 50
  have he' : (p^(1/50:ℝ))^50=p := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hp.le]; norm_num
  rw [mul_pow,he',←pow_mul] at Hpow
  norm_num only [Nat.mul_one] at Hpow
  apply (le_div_iff₀ (pow_pos hb 100)).mpr
  nlinarith only [Hpow]
end NeutralAtom

namespace NeutralAtom
lemma le_discrete_tail_sum (t : ℕ → ℝ) (ht : ∀ k, 0 ≤ t k)
    {x : ℝ} (_ : 0 ≤ x) (N : ℕ) (hxN : x ≤ t N) :
    x ≤ t 0+∑ k∈Finset.range N,t (k+1)*(if t k<x then 1 else 0) := by
  induction N with
  | zero => simpa using hxN
  | succ N ih =>
    rw [Finset.sum_range_succ]
    by_cases h : x ≤ t N
    · have hn : 0 ≤ t (N+1)*(if t N<x then 1 else 0) := by split_ifs <;> simp only [mul_one,mul_zero]; exact ht _; exact le_rfl
      linarith [ih h]
    · rw [ite_eq_left (lt_of_not_ge h),mul_one]
      have hsum : 0 ≤ ∑ k∈Finset.range N,t (k+1)*(if t k<x then 1 else 0) := by
        apply Finset.sum_nonneg
        intro k _
        split_ifs <;> simp only [mul_one,mul_zero]; exact ht _; exact le_rfl
      linarith [ht 0]

lemma firstMoment_le_discrete_tails {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : Measurable f)
    (hf0 : ∀ z,0 ≤ f z) (t b : ℕ → ℝ) (ht : ∀ k,0 ≤ t k)
    (N : ℕ) (hbound : ∀ z,f z ≤ t N)
    (htail : ∀ k,P.real {z | t k<f z} ≤ b k)
    (hsum : Summable (fun k => t (k+1)*b k)) :
    (∫ z,f z ∂P) ≤ t 0+∑' k,t (k+1)*b k := by
  let F : ℕ → Ω → ℝ := fun k => ({z | t k<f z}).indicator (fun _ => (1:ℝ))
  have hF : ∀ k,Integrable (F k) P := fun k =>
    (integrable_const 1).indicator (measurableSet_lt measurable_const hf)
  have hfi : Integrable f P := by
    apply Integrable.of_bound hf.aestronglyMeasurable (t N)
    exact Eventually.of_forall (fun z => by rw [Real.norm_of_nonneg (hf0 z)]; exact hbound z)
  have hgi : Integrable (fun z => t 0+∑ k∈Finset.range N,t (k+1)*F k z) P :=
    (integrable_const _).add (integrable_finsetSum _ (fun k _ => (hF k).const_mul _))
  have H := integral_mono hfi hgi (fun z => le_discrete_tail_sum t ht (hf0 z) N (hbound z))
  have he : (∫ z,t 0+∑ k∈Finset.range N,t (k+1)*F k z ∂P)=
      t 0+∑ k∈Finset.range N,t (k+1)*P.real {z | t k<f z} := by
    rw [integral_add (integrable_const _) (integrable_finsetSum _ (fun k _ => (hF k).const_mul _)),
      integral_finsetSum _ (fun k _ => (hF k).const_mul _)]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_const_mul]
    congr 1
    exact integral_indicator_const _ (measurableSet_lt measurable_const hf) |>.trans (by simp)
  rw [he] at H
  apply H.trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ k∈Finset.range N,t (k+1)*b k :=
      Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (htail k) (ht _))
    _ ≤ ∑' k,t (k+1)*b k :=
      hsum.sum_le_tsum _ (fun k _ => mul_nonneg (ht _) (measureReal_nonneg.trans (htail k)))

lemma positive_part_tail {Ω : Type*} (f : Ω → ℝ) {C k : ℝ} (hk : 0 ≤ k) :
    {z | k < max (f z-C) 0}={z | C+k < f z} := by
  ext z
  simp only [mem_ofPred_eq,lt_max_iff,not_lt_of_ge hk,or_false]
  constructor <;> intro h <;> linarith

theorem logarithmic_tail_integral : ∃ K : ℝ,0 < K ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {f : Ω → ℝ}, Measurable f → ∀ {B C d : ℝ}, (∀ z,f z ≤ B) → 1 ≤ C → 0 ≤ d →
    (∀ b : ℝ,2*C ≤ b → 0 < P.real {z | b<f z} →
      (b-C)^2 ≤ d*(1-Real.log (P.real {z | b<f z}))^5) →
    (∫ z,max (f z-2*C) 0 ∂P) ≤ K*d^50 := by
  let W := fun k : ℕ => ((k:ℝ)+1)^(-99:ℝ)
  have hW : Summable W := by
    have H := (Real.summable_nat_rpow.mpr (by norm_num : (-99:ℝ) < -1))
    simpa only [W,Nat.cast_add,Nat.cast_one] using (summable_nat_add_iff 1).mpr H
  let K : ℝ := 251^(250:ℕ)*((∑' k,W k)+1)
  have hW0 : ∀ k,0 ≤ W k := fun k => by dsimp [W]; positivity
  have hK : 0 < K := mul_pos (pow_pos (by norm_num) 250) (by have h : 0 ≤ ∑' k,W k := tsum_nonneg hW0; linarith)
  refine ⟨K,hK,?_⟩
  intro Ω inst P instP f hf B C d hB hC hd hprob
  let A : ℝ := (251^5*d)^50
  have hA : 0 ≤ A := pow_nonneg (mul_nonneg (pow_nonneg (by norm_num) 5) hd) 50
  let t : ℕ → ℝ := fun k => k
  let b : ℕ → ℝ := fun k => A/((k:ℝ)+1)^100
  have hsEq (k : ℕ) : t (k+1)*b k=A*W k := by
    have hk : (k:ℝ)+1 ≠ 0 := by positivity
    simp only [t,b,W,Nat.cast_add,Nat.cast_one]
    rw [show (-99:ℝ)= -((99:ℕ):ℝ) by norm_num,Real.rpow_neg_natCast]
    simp only [zpow_neg,zpow_natCast]
    rw [show (((k:ℝ)+1)^100)=((k:ℝ)+1)*((k:ℝ)+1)^99 by rw [pow_succ']]
    field_simp [hk]
  have hsum : Summable (fun k => t (k+1)*b k) := by
    simp_rw [hsEq]
    exact hW.mul_left A
  have htail (k : ℕ) : P.real {z | t k < max (f z-2*C) 0} ≤ b k := by
    rw [positive_part_tail f (show 0 ≤ t k from Nat.cast_nonneg k)]
    by_cases hp : 0 < P.real {z | 2*C+(k:ℝ)<f z}
    · have H := probability_of_log_fifth hp (measureReal_le_one)
        (by have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg k; linarith : 0 < (2*C+(k:ℝ))-C) hd
        (hprob (2*C+k) (by have hk := Nat.cast_nonneg (α:=ℝ) k; linarith) hp)
      apply H.trans
      apply div_le_div_of_nonneg_left hA (by positivity)
      apply pow_le_pow_left₀ (by positivity : 0 ≤ (k:ℝ)+1)
      linarith
    · have he : P.real {z | 2*C+(k:ℝ)<f z}=0 := le_antisymm (le_of_not_gt hp) measureReal_nonneg
      change P.real {z | 2*C+(k:ℝ)<f z} ≤ _
      rw [he]
      exact div_nonneg hA (pow_nonneg (by positivity) 100)
  obtain ⟨N,hN⟩ := exists_nat_ge B
  have hbnd (z : Ω) : max (f z-2*C) 0 ≤ t N := by
    apply max_le
    · dsimp [t]; linarith [hB z]
    · exact Nat.cast_nonneg N
  have H := firstMoment_le_discrete_tails P ((hf.sub measurable_const).max measurable_const)
    (fun _ => le_max_right _ _) t b (fun k => Nat.cast_nonneg k) N hbnd htail hsum
  simp_rw [hsEq,tsum_mul_left] at H
  simp only [t,Nat.cast_zero,zero_add] at H
  apply H.trans
  have he : A=251^(250:ℕ)*d^50 := by dsimp [A]; rw [mul_pow,←pow_mul]
  rw [he]
  dsimp [K]
  calc
    _ ≤ 251^250*d^50*((∑' k,W k)+1) := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (mul_nonneg (pow_nonneg (by norm_num) 250) (pow_nonneg hd 50))
    _ = _ := by ac_rfl
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_ScaledFieldCap
attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace NeutralAtom

lemma physicalFieldCapUnit_pos : 0 < physicalFieldCapUnit := by
  have h : 0 < Coulomb.atomicBudgetRecursionC := lt_of_lt_of_le (by norm_num) Coulomb.atomicBudgetRecursionC_ge_four
  have hP : 0 < Coulomb.atomicCountConstant := lt_of_lt_of_le (by norm_num) Coulomb.atomicCountConstant_ge_two
  unfold physicalFieldCapUnit
  positivity

lemma scaled_screen_field {a δ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (_ : 0 ≤ δ) :
    (100000*a)^4*(2*Coulomb.atomicBudgetRecursionC^2*
      Coulomb.screenFieldUnit δ Coulomb.atomicCountConstant a)=
    physicalFieldCapUnit*(1+Real.sqrt (δ*a^7)) := by
  have hpow : a^3 ≤ 1 := pow_le_one₀ ha.le ha1
  have hinv : 1 ≤ (a^3)⁻¹ := (one_le_inv₀ (pow_pos ha 3)).mpr hpow
  have hsqrt : Real.sqrt (δ*a^7)=a^3*Real.sqrt (δ*a) := by
    rw [show δ*a^7=(a^3)^2*(δ*a) by ring, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (pow_nonneg ha.le 3)]
  unfold Coulomb.screenFieldUnit Coulomb.screenMass Coulomb.screenBaseMass physicalFieldCapUnit
  rw [max_eq_left hinv,hsqrt]
  field_simp [ha.ne']

lemma scaled_screen_field_log {a D Q : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hD : 0 ≤ D) (hQ : 0 ≤ Q) (hDa : D*a^7 ≤ 1) :
    (100000*a)^4*(2*Coulomb.atomicBudgetRecursionC^2*
      Coulomb.screenFieldUnit (D+Q) Coulomb.atomicCountConstant a) ≤
    2*physicalFieldCapUnit+physicalFieldCapUnit*Real.sqrt (Q*a^7) := by
  rw [scaled_screen_field ha ha1 (add_nonneg hD hQ),add_mul]
  have hs : Real.sqrt (D*a^7+Q*a^7) ≤ 1+Real.sqrt (Q*a^7) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt (mul_nonneg hQ (pow_nonneg ha.le 7)),Real.sqrt_nonneg (Q*a^7)]
  have hC := physicalFieldCapUnit_pos.le
  nlinarith [mul_le_mul_of_nonneg_left hs hC]

lemma cap_square_of_mean {b C Q a : ℝ} (_ : 0 ≤ C) (hQ : 0 ≤ Q) (ha : 0 ≤ a)
    (hb : 2*C ≤ b) (hh : b ≤ 2*C+C*Real.sqrt (Q*a^7)) :
    (b-2*C)^2 ≤ C^2*Q*a^7 := by
  have ht : 0 ≤ b-2*C := by linarith
  have hle : b-2*C ≤ C*Real.sqrt (Q*a^7) := by linarith
  have H := pow_le_pow_left₀ ht hle 2
  rw [mul_pow,Real.sq_sqrt (mul_nonneg hQ (pow_nonneg ha 7))] at H
  nlinarith only [H]
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap
noncomputable section
namespace NeutralAtom

theorem physical_retained_field_tail (g₀ : 𝓢(Position,ℝ))
    (hg : ∀ z,1 < ‖z‖ → g₀ z=0) (hm : (∫ z,g₀ z^2)=1)
    (hrad : ∀ z,g₀ z=g₀ (EuclideanSpace.single 0 ‖z‖))
    {n J : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (hn : normSquared ψ=1)
    (hmin : ∀ (χ : Wavefunction n) (h : Gradient n), FormDomain χ h → normSquared χ=1 →
      energy Z ψ g ≤ energy Z χ h)
    {E D : ℝ} (hE : (E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ))
    (hbase : energy Z ψ g ≤ E+D) (hD : 0 ≤ D)
    (r : Fin J → ℝ) (hr : ∀ k,0 < r k) (j : ℕ)
    {c r₀ s : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀) (hs : 0 < s)
    (hscale : c*(1+packetExponent)*s^packetExponent ≤ 1/2)
    (y : Position) (hy : y≠0) (ha1 : Coulomb.atomicCellScale y ≤ 1)
    (hDa : D*(Coulomb.atomicCellScale y)^7 ≤ 1)
    (hwidth : 2*packetWidth c r₀ s y ≤ 40*Coulomb.atomicCellScale y) :
    letI := rawLaw_isProbability hd.2.2.1 hn
    let P := observationLaw J (rawLaw ψ)
    let f := fun z : ObservationSample n J => ‖y‖^4*((Z:ℝ)*coulombKernel y-
      potentialOf (conditionalPacketDensity P Prod.fst (tailObservation r j) g₀ c r₀ s
        (tailObservation r j z)) y)
    ∀ {b : ℝ}, 2*physicalFieldCapUnit ≤ b → 0 < P.real {z | b < f z} →
      (b-2*physicalFieldCapUnit)^2 ≤
        (physicalFieldCapUnit^2*observationEventEnergyConstant*
          observationWidthSquareSum (fun k : RetainedScales J j => (r k.val)^(101/100:ℝ))*
          (Coulomb.atomicCellScale y)^7)*(1-Real.log (P.real {z | b < f z}))^5 := by
  have := rawLaw_isProbability hd.2.2.1 hn
  dsimp only
  intro b hb hp
  let P := observationLaw J (rawLaw ψ)
  let obs : ObservationSample n J → Fin J → UnorderedArray n := tailObservation r j
  let F := fun datum => (Z:ℝ)*coulombKernel y-
    potentialOf (conditionalPacketDensity P Prod.fst obs g₀ c r₀ s datum) y
  let B := {datum | b < ‖y‖^4*F datum}
  have hgs : HasCompactSupport (g₀ : Position → ℝ) :=
    HasCompactSupport.intro (isCompact_closedBall (0:Position) 1) (fun z hz =>
      hg z (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz))
  have hF : Measurable F := measurable_const.sub
    (measurable_conditionalPacketPotential_data P Prod.fst obs g₀.continuous hgs hm hc hr₀ hs y)
  have hB : MeasurableSet B := measurableSet_lt measurable_const (hF.const_mul _)
  have hpEq := physical_retainedTailEvent_probability hd.2.2.1 hn r hr j hB
  change 0 < P.real (obs ⁻¹' B) at hp
  have hp1 : P.real (obs ⁻¹' B) ≤ 1 := measureReal_le_one
  let p := P.real (obs ⁻¹' B)
  let Q := observationEventEnergyConstant*
    observationWidthSquareSum (fun k : RetainedScales J j => (r k.val)^(101/100:ℝ))*(1-Real.log p)^5
  have hlog : 0 ≤ 1-Real.log p := by linarith [Real.log_nonpos hp.le hp1]
  have hQ : 0 ≤ Q := mul_nonneg (mul_nonneg observationEventEnergyConstant_pos.le
    (observationWidthSquareSum_nonneg _)) (pow_nonneg hlog 5)
  obtain ⟨u,hu,hum,hue,hlaw⟩ := atomic_arrayEvent_state Z hZ hd hn hmin hbase
    (fun k : RetainedScales J j => (r k.val)^(101/100:ℝ))
    (fun k => Real.rpow_pos_of_pos (hr k.val) _)
    (hB.preimage (measurable_retainedTailObservation j))
    (fun p z => by simp only [mem_preimage,retainedTailObservation_permute])
    (hpEq ▸ hp)
  have hue' : Coulomb.form (Coulomb.atom Z hZ) u ≤ E+(D+Q) := by
    simpa only [←hpEq] using hue
  have Hcap := atomic_master_field_cap (Coulomb.atom Z hZ) (by intro i; rfl)
    u hu hum hE hue' (add_nonneg hD hQ) g₀ hm hrad hg hc hr₀ hs hscale y hy hwidth
  have Htower := retainedEvent_field_mean hd.2.2.1 hn r hr j hB u hum hlaw hp
    g₀.continuous hgs hm hc hr₀ hs y ((Z:ℝ)*coulombKernel y)
  have hatt : Coulomb.attraction (Coulomb.atom Z hZ) y=(Z:ℝ)*coulombKernel y := by
    simp [Coulomb.attraction,Coulomb.atom,Coulomb.coulombKernel,coulombKernel]
  rw [hatt,Htower] at Hcap
  have hfi : Integrable (fun z => F (obs z)) P :=
    (integrable_const _).sub (conditionalPacketPotential_integrable P (rawLaw ψ)
      (observationLaw_rawProjection _) (measurable_tailObservation r j) g₀.continuous hgs hm hc hr₀ hs y)
  have Hlow := le_normalized_event (hB.preimage (measurable_tailObservation r j))
    (hfi.const_mul (‖y‖^4)) hp (v:=b)
    (Eventually.of_forall (fun z hz => (show b < ‖y‖^4*F (obs z) from hz).le))
  rw [integral_const_mul] at Hlow
  have Hs := mul_le_mul_of_nonneg_left Hcap (pow_nonneg (norm_nonneg y) 4)
  have he : ‖y‖=100000*Coulomb.atomicCellScale y := by unfold Coulomb.atomicCellScale; ring
  have Hlog := scaled_screen_field_log (Coulomb.atomicCellScale_pos hy) ha1 hD hQ hDa
  rw [←he] at Hlog
  have hb' : b ≤ 2*physicalFieldCapUnit+physicalFieldCapUnit*Real.sqrt (Q*(Coulomb.atomicCellScale y)^7) := by
    exact (Hlow.trans (by simpa only [mul_left_comm] using Hs)).trans Hlog
  have H := cap_square_of_mean physicalFieldCapUnit_pos.le hQ
    (Coulomb.atomicCellScale_pos hy).le hb hb'
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [Q,p,P,obs,B,F]
  ring
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_PhysicalCapMoment
attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap
noncomputable section
namespace NeutralAtom

lemma physicalFieldCapBase_ge_one : 1 ≤ physicalFieldCapBase := le_max_left _ _
lemma physicalFieldCapBase_ge_unit : 2*physicalFieldCapUnit ≤ physicalFieldCapBase := le_max_right _ _

theorem physical_retained_field_excess_moment : ∃ K : ℝ,0 < K ∧
    ∀ (g₀ : 𝓢(Position,ℝ)), (∀ z,1 < ‖z‖ → g₀ z=0) → (∫ z,g₀ z^2)=1 →
    (∀ z,g₀ z=g₀ (EuclideanSpace.single 0 ‖z‖)) →
    ∀ {n J : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction n} {g : Gradient n},
    ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
    (∀ (χ : Wavefunction n) (h : Gradient n), FormDomain χ h → normSquared χ=1 →
      energy Z ψ g ≤ energy Z χ h) →
    ∀ {E D : ℝ}, (E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E+D → 0 ≤ D → ∀ (r : Fin J → ℝ), (∀ k,0 < r k) → ∀ (j : ℕ),
    ∀ {c r₀ s : ℝ}, 0 < c → 0 < r₀ → 0 < s →
    c*(1+packetExponent)*s^packetExponent ≤ 1/2 →
    ∀ (y : Position), y≠0 → Coulomb.atomicCellScale y ≤ 1 →
    D*(Coulomb.atomicCellScale y)^7 ≤ 1 →
    2*packetWidth c r₀ s y ≤ 40*Coulomb.atomicCellScale y →
    letI := rawLaw_isProbability hd.2.2.1 hn
    let P := observationLaw J (rawLaw ψ)
    (∫ z,max (‖y‖^4*((Z:ℝ)*coulombKernel y-
      potentialOf (conditionalPacketDensity P Prod.fst (tailObservation r j) g₀ c r₀ s
        (tailObservation r j z)) y)-2*physicalFieldCapBase) 0 ∂P) ≤
      K*(physicalFieldCapUnit^2*observationEventEnergyConstant*
          observationWidthSquareSum (fun k : RetainedScales J j => (r k.val)^(101/100:ℝ))*
          (Coulomb.atomicCellScale y)^7)^50 := by
  obtain ⟨K,hK,HK⟩ := logarithmic_tail_integral
  refine ⟨K,hK,?_⟩
  intro g₀ hg hm hrad n J Z hZ ψ g hd hn hmin E D hE hbase hD r hr j c r₀ s hc hr₀ hs hscale y hy ha1 hDa hwidth
  have := rawLaw_isProbability hd.2.2.1 hn
  dsimp only
  let P := observationLaw J (rawLaw ψ)
  let μ := conditionalPacketDensity P Prod.fst (tailObservation r j) g₀ c r₀ s
  let f := fun z : ObservationSample n J => ‖y‖^4*((Z:ℝ)*coulombKernel y-potentialOf (μ (tailObservation r j z)) y)
  have hgs : HasCompactSupport (g₀ : Position → ℝ) :=
    HasCompactSupport.intro (isCompact_closedBall (0:Position) 1) (fun z hz =>
      hg z (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz))
  have hf : Measurable f := ((measurable_const.sub
    (measurable_conditionalPacketPotential_data P Prod.fst (tailObservation r j)
      g₀.continuous hgs hm hc hr₀ hs y)).comp (measurable_tailObservation r j)).const_mul _
  have hB (z : ObservationSample n J) : f z ≤ ‖y‖^4*((Z:ℝ)*coulombKernel y) := by
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (norm_nonneg y) 4)
    have hpot := potentialOf_nonneg (conditionalPacketDensity_nonneg P Prod.fst
      (tailObservation r j) g₀ hc hr₀ hs (tailObservation r j z)) y
    linarith
  apply HK P hf hB physicalFieldCapBase_ge_one
    (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) observationEventEnergyConstant_pos.le)
      (observationWidthSquareSum_nonneg _)) (pow_nonneg (Coulomb.atomicCellScale_pos hy).le 7))
  intro b hb hp
  have hC0 : 0 ≤ physicalFieldCapBase := zero_le_one.trans physicalFieldCapBase_ge_one
  have hb' : physicalFieldCapBase ≤ b := by linarith
  have H := physical_retained_field_tail g₀ hg hm hrad Z hZ hd hn hmin hE hbase hD
    r hr j hc hr₀ hs hscale y hy ha1 hDa hwidth
    (physicalFieldCapBase_ge_unit.trans hb') hp
  apply le_trans _ H
  apply pow_le_pow_left₀ (by linarith : 0 ≤ b-physicalFieldCapBase)
  linarith [physicalFieldCapBase_ge_unit]
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace NeutralAtom
lemma cap_scale_power {r : ℝ} (hr : 0 < r) :
    ((((r^(101/100:ℝ))⁻¹)^2)*r^7)^50=r^249 := by
  rw [←Real.rpow_neg hr.le,←Real.rpow_natCast _ 2,←Real.rpow_mul hr.le,
    ←Real.rpow_natCast r 7,←Real.rpow_add hr,←Real.rpow_natCast _ 50,←Real.rpow_mul hr.le]
  norm_num

lemma cap_moment_factor {r a A C S : ℝ} (hr : 0 < r) (ha : 0≤a)
    (_ : 0≤A) (hC : 0≤C) (hS : 0≤S) (haA : a≤A*r)
    (hwidth : S≤(4/3:ℝ)*((r^(101/100:ℝ))⁻¹)^2) :
    (C*S*a^7)^50≤((4/3:ℝ)*C*A^7)^50*r^249 := by
  have hp : a^7≤A^7*r^7 := by simpa only [mul_pow] using pow_le_pow_left₀ ha haA 7
  have h1 := mul_le_mul (mul_le_mul_of_nonneg_left hwidth hC) hp
    (pow_nonneg ha 7) (by positivity : 0≤C*((4/3:ℝ)*((r^(101/100:ℝ))⁻¹)^2))
  have h2 : C*S*a^7≤((4/3:ℝ)*C*A^7)*(((r^(101/100:ℝ))⁻¹)^2*r^7) := by
    calc
      _ ≤ C*((4/3:ℝ)*((r^(101/100:ℝ))⁻¹)^2)*(A^7*r^7) := h1
      _ = _ := by ring
  have h3 := pow_le_pow_left₀ (by positivity : 0≤C*S*a^7) h2 50
  rw [mul_pow ((4/3:ℝ)*C*A^7),cap_scale_power hr] at h3
  exact h3

lemma cap_annulus_compact (r L : ℝ) :
    IsCompact {z : Position | r/2≤‖z‖ ∧ ‖z‖≤8*L*r} := by
  apply (isCompact_closedBall (0:Position) (8*L*r)).of_isClosed_subset
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  · intro z hz
    simpa only [Metric.mem_closedBall,dist_zero_right] using hz.2

lemma cap_annulus_volume_ratio {r L : ℝ} (hr : 0 < r) (hL : 1≤L) :
    volume.real {z : Position | r/2≤‖z‖ ∧ ‖z‖≤8*L*r}/
      (4*Real.pi/3*(r/8)^3)≤(64*L)^3 := by
  have hR : 0≤8*L*r := by positivity
  have hV : 0<4*Real.pi/3*(r/8)^3 := by positivity
  have H : volume.real {z : Position | r/2≤‖z‖ ∧ ‖z‖≤8*L*r}≤
      volume.real (Metric.closedBall (0:Position) (8*L*r)) := by
    apply measureReal_mono ?_ (isCompact_closedBall (0:Position) (8*L*r)).measure_ne_top
    intro z hz
    simpa only [Metric.mem_closedBall,dist_zero_right] using hz.2
  rw [Coulomb.volume_closedBall_three _ hR] at H
  apply (div_le_iff₀ hV).2
  have he : (64*L)^3*(4*Real.pi/3*(r/8)^3)=4*Real.pi/3*(8*L*r)^3 := by ring
  rw [he]
  exact H
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PosteriorSpatialCap
attribute [-instance] _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace NeutralAtom

lemma posterior_scaled_excess_bounded {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (raw : Ω → Configuration n) (obs : Ω → B)
    (g : Position → ℝ) {c r₀ s : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀) (hs : 0 < s)
    (datum : B) {Z r L T : ℝ} (hZ : 0≤Z) (hr : 0 < r) (hL : 1≤L) (hT : 0≤T)
    {y : Position} (hy0 : r/2≤‖y‖) (hy1 : ‖y‖≤8*L*r) :
    max (‖y‖^4*(Z*coulombKernel y-potentialOf
      (conditionalPacketDensity P raw obs g c r₀ s datum) y)-T) 0 ≤ Z*(8*L*r)^3 := by
  have hp := potentialOf_nonneg (conditionalPacketDensity_nonneg P raw obs g hc hr₀ hs datum) y
  have hn : 0<‖y‖ := by linarith
  have he : ‖y‖^4*coulombKernel y=‖y‖^3 := by unfold coulombKernel; field_simp
  have hab : ‖y‖^4*(Z*coulombKernel y-potentialOf
      (conditionalPacketDensity P raw obs g c r₀ s datum) y)≤Z*‖y‖^3 := by
    have H := mul_le_mul_of_nonneg_left (sub_le_self (Z*coulombKernel y) hp) (pow_nonneg hn.le 4)
    calc
      _ ≤ ‖y‖^4*(Z*coulombKernel y) := H
      _ = Z*‖y‖^3 := by rw [mul_left_comm,he]
  have hcub := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn.le hy1 3) hZ
  apply max_le
  · linarith
  · positivity

lemma posterior_spatial_cap_of_moment {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B] {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (raw : Ω → Configuration n)
    (obs : Ω → B) (hobs : Measurable obs)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g)
    (hm : (∫ z,g z^2)=1) {c r₀ s : ℝ}
    (hc : 0 < c) (hr₀ : 0 < r₀) (hs : 0 < s)
    {Z r L M : ℝ} (hZ : 0≤Z) (hr : 0 < r) (hL : 1≤L) (hM0 : 0≤M)
    (hM : ∀ y : Position,r/2≤‖y‖ → ‖y‖≤8*L*r →
      (∫ ω,max (‖y‖^4*(Z*coulombKernel y-potentialOf
        (conditionalPacketDensity P raw obs g c r₀ s (obs ω)) y)-2*physicalFieldCapBase) 0 ∂P)≤M) :
    ∃ G : Set Ω,(MeasurableSet G ∧ MeasurableSet[MeasurableSpace.comap obs ‹MeasurableSpace B›] G) ∧ P.real Gᶜ≤16*(64*L)^3*M ∧
      ∀ ω∈G,∀ y : Position,3*r/4≤‖y‖ → ‖y‖≤6*L*r →
        ‖y‖^4*(Z*coulombKernel y-potentialOf
          (conditionalPacketDensity P raw obs g c r₀ s (obs ω)) y)≤physicalSpatialCap := by
  let F := fun ω y => Z*coulombKernel y-potentialOf
    (conditionalPacketDensity P raw obs g c r₀ s (obs ω)) y
  let T := 2*physicalFieldCapBase
  let A := {y : Position | r/2≤‖y‖ ∧ ‖y‖≤8*L*r}
  let Q := fun wy : Ω × Position => max (‖wy.2‖^4*F wy.1 wy.2-T) 0
  let V := 4*Real.pi/3*(r/8)^3
  have hV : 0<V := by dsimp [V]; positivity
  have hT : 0≤T := by dsimp [T]; linarith [physicalFieldCapBase_ge_one]
  have hA : IsCompact A := cap_annulus_compact r L
  have hFmeas : Measurable (fun wy : Ω × Position => F wy.1 wy.2) := by
    have hp := measurable_conditionalPacketPotential_joint P raw obs hg hgs hm hc hr₀ hs
    have hcmeas : Measurable (fun wy : Ω × Position =>
        potentialOf (conditionalPacketDensity P raw obs g c r₀ s (obs wy.1)) wy.2) := by
      change Measurable ((fun dy : B × Position =>
        potentialOf (conditionalPacketDensity P raw obs g c r₀ s dy.1) dy.2) ∘
          (fun wy : Ω × Position => (obs wy.1,wy.2)))
      exact hp.comp ((hobs.comp measurable_fst).prodMk measurable_snd)
    exact ((measurable_coulombKernel.comp measurable_snd).const_mul Z).sub hcmeas
  have hQmeas : Measurable Q :=
    (((measurable_snd.norm.pow_const 4).mul hFmeas).sub_const T).max measurable_const
  have hQ0 : ∀ wy,0≤Q wy := fun _ => le_max_right _ _
  have HB : ∀ ω y,y∈A → Q (ω,y)≤Z*(8*L*r)^3 := by
    intro ω y hy
    exact posterior_scaled_excess_bounded P raw obs g hc hr₀ hs (obs ω) hZ hr hL hT hy.1 hy.2
  obtain ⟨hI,hi,hprob⟩ := spatial_moment_markov P hA.measurableSet hA.measure_lt_top
    hQmeas hQ0 HB (fun y hy => hM y hy.1 hy.2) (div_pos hV (by norm_num : (0:ℝ)<16))
  let G := {ω | (∫ y in A,Q (ω,y))≤V/16}
  have hIdata : Measurable (fun datum : B => ∫ y in A,
      max (‖y‖^4*(Z*coulombKernel y-potentialOf
        (conditionalPacketDensity P raw obs g c r₀ s datum) y)-T) 0) := by
    have hp := measurable_conditionalPacketPotential_joint P raw obs hg hgs hm hc hr₀ hs
    have hq : Measurable (fun dy : B × Position => max (‖dy.2‖^4*(Z*coulombKernel dy.2-potentialOf
      (conditionalPacketDensity P raw obs g c r₀ s dy.1) dy.2)-T) 0) :=
      (((measurable_snd.norm.pow_const 4).mul
      (((measurable_coulombKernel.comp measurable_snd).const_mul Z).sub hp)).sub_const T).max measurable_const
    exact hq.stronglyMeasurable.integral_prod_right'.measurable
  have hGtail : MeasurableSet[MeasurableSpace.comap obs ‹MeasurableSpace B›] G := by
    exact ⟨{datum : B | (∫ y in A,max (‖y‖^4*(Z*coulombKernel y-potentialOf
      (conditionalPacketDensity P raw obs g c r₀ s datum) y)-T) 0)≤V/16},
      measurableSet_le hIdata measurable_const,rfl⟩
  refine ⟨G,⟨measurableSet_le hI measurable_const,hGtail⟩,?_,?_⟩
  · have hGe : Gᶜ={ω | V/16<(∫ y in A,Q (ω,y))} := by ext ω; simp only [G,mem_compl_iff,mem_ofPred_eq,not_le]
    rw [hGe]
    apply hprob.trans
    have hv := cap_annulus_volume_ratio hr hL
    have he : volume.real A*M/(V/16)=16*(volume.real A/V)*M := by ring
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_right hv hM0]
  · intro ω hω y hy0 hy1
    have hFn : ContinuousOn (F ω) (Metric.closedBall y (r/8)) := by
      apply (continuousOn_const.mul (continuous_norm.continuousOn.inv₀ ?_)).sub
        (conditionalPacketPotential_continuous P raw obs hg hgs hm hc hr₀ hs (obs ω)).continuousOn
      intro z hz
      have hn := (cap_ball_geometry hr hL hy0 hy1 hz).1
      have hz0 : 0<‖z‖ := by linarith
      exact ne_of_gt hz0
    have hmean := conditionalPacketField_submean P raw obs hg hgs hm hc hr₀ hs
      (obs ω) Z (div_pos hr (by norm_num : (0:ℝ)<8)) y (by linarith : r/8≤‖y‖)
    have H := annular_submean_cap hr hL hT (hi ω) hy0 hy1
      (hFn.integrableOn_compact (isCompact_closedBall _ _)) hmean
    have hω' : (∫ z in A,Q (ω,z))≤V/16 := hω
    have hsmall : 16*V⁻¹*(∫ z in A,Q (ω,z))≤1 := by
      have hh := mul_le_mul_of_nonneg_left hω' (by positivity : 0≤16*V⁻¹)
      have he : 16*V⁻¹*(V/16)=1 := by field_simp
      exact hh.trans_eq he
    change ‖y‖^4*F ω y≤physicalSpatialCap
    change ‖y‖^4*F ω y≤16*T+16*V⁻¹*(∫ z in A,Q (ω,z)) at H
    dsimp [physicalSpatialCap,T] at *
    linarith
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_PhysicalSpatialCap
attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical SchwartzMap
noncomputable section
namespace NeutralAtom

theorem physical_retained_spatial_cap_oai {L : ℝ} (hL : 1 ≤ L) :
    ∃ C : ℝ,0 < C ∧
    ∀ (g₀ : 𝓢(Position,ℝ)), (∀ z,1 < ‖z‖ → g₀ z=0) → (∫ z,g₀ z^2)=1 →
    (∀ z,g₀ z=g₀ (EuclideanSpace.single 0 ‖z‖)) →
    ∀ {n J : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction n} {g : Gradient n},
    ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
    (∀ (χ : Wavefunction n) (h : Gradient n),FormDomain χ h → normSquared χ=1 →
      energy Z ψ g ≤ energy Z χ h) →
    ∀ {E D : ℝ}, (E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E+D → 0 ≤ D →
    ∀ {c r₀ s : ℝ},0 < c → 0 < r₀ → 0 < s →
    c*(1+packetExponent)*s^packetExponent ≤ 1/2 →
    100000*c*s^packetExponent ≤ 10 →
    (8*L/100000)*s ≤ 1 → D*((8*L/100000)*s)^7 ≤ 1 →
    ∀ (j : ℕ),r₀*2^j ≤ s →
    letI := rawLaw_isProbability hd.2.2.1 hn
    let P := observationLaw J (rawLaw ψ)
    let r := fun k : Fin J =>  r₀*2^k.val
    ∃ G : Set (ObservationSample n J),(MeasurableSet G ∧
      MeasurableSet[MeasurableSpace.comap (tailObservation r j) inferInstance] G) ∧
      P.real Gᶜ ≤ C*(r₀*2^j)^249 ∧
      ∀ z∈G,∀ y : Position,3*(r₀*2^j)/4 ≤ ‖y‖ → ‖y‖ ≤ 6*L*(r₀*2^j) →
        ‖y‖^4*((Z:ℝ)*coulombKernel y-potentialOf
          (conditionalPacketDensity P Prod.fst (tailObservation r j) g₀ c r₀ s
            (tailObservation r j z)) y) ≤ physicalSpatialCap := by
  obtain ⟨K,hK,HK⟩ := physical_retained_field_excess_moment
  let A := 8*L/100000
  let B := physicalFieldCapUnit^2*observationEventEnergyConstant
  let C₀ := K*((4/3:ℝ)*B*A^7)^50
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; exact mul_pos (sq_pos_of_pos physicalFieldCapUnit_pos) observationEventEnergyConstant_pos
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  refine ⟨16*(64*L)^3*C₀,by positivity,?_⟩
  intro g₀ hg hm hrad n J Z hZ ψ g hd hn hmin E D hE hb hD c r₀ s hc hr₀ hs hscale hw hsA hsD j hrj
  have := rawLaw_isProbability hd.2.2.1 hn
  dsimp only
  let P := observationLaw J (rawLaw ψ)
  let r : Fin J → ℝ := fun k =>  r₀*2^k.val
  let R := r₀*2^j
  have hR : 0 < R := by dsimp [R]; positivity
  have hrR : r₀ ≤ R := le_mul_of_one_le_right hr₀.le (one_le_pow₀ (by norm_num))
  have hgs : HasCompactSupport (g₀ : Position → ℝ) :=
    HasCompactSupport.intro (isCompact_closedBall (0:Position) 1) (fun z hz =>
      hg z (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz))
  have hmoment (y : Position) (hy0 : R/2 ≤ ‖y‖) (hy1 : ‖y‖ ≤ 8*L*R) :
      (∫ z,max (‖y‖^4*((Z:ℝ)*coulombKernel y-potentialOf
        (conditionalPacketDensity P Prod.fst (tailObservation r j) g₀ c r₀ s
          (tailObservation r j z)) y)-2*physicalFieldCapBase) 0 ∂P)  ≤  C₀*R^249 := by
    have hyn : 0 < ‖y‖ := by linarith
    have hy : y≠0 := norm_pos_iff.mp hyn
    let a := Coulomb.atomicCellScale y
    have ha : 0 < a := Coulomb.atomicCellScale_pos hy
    have haR : a ≤ A*R := by dsimp [a,A,Coulomb.atomicCellScale]; linarith
    have haS : a ≤ A*s := haR.trans (mul_le_mul_of_nonneg_left hrj hA.le)
    have ha1 : a ≤ 1 := haS.trans hsA
    have hDa : D*a^7 ≤ 1 :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le haS 7) hD).trans hsD
    have hmax : max ‖y‖ r₀ ≤ 2*‖y‖ := max_le (by linarith) (by linarith)
    have hp := (packetWidth_le c r₀ s hc.le hr₀ hs y).trans
      (mul_le_mul_of_nonneg_left hmax (by positivity))
    have hwidth : 2*packetWidth c r₀ s y ≤ 40*a := by
      have hmul := mul_le_mul_of_nonneg_right hw hyn.le
      dsimp [a,Coulomb.atomicCellScale]
      nlinarith
    have H := HK g₀ hg hm hrad Z hZ hd hn hmin hE hb hD r
      (fun _ =>  by dsimp [r]; positivity) j hc hr₀ hs hscale y hy ha1 hDa hwidth
    apply H.trans
    have Hfac := cap_moment_factor hR ha.le hA.le hB.le
      (observationWidthSquareSum_nonneg (fun k : RetainedScales J j =>  (r k.val)^(101/100:ℝ)))
      haR (observationWidthSquareSum_retained_dyadic hr₀ J j)
    have Hmul := mul_le_mul_of_nonneg_left Hfac hK.le
    change K*(B*observationWidthSquareSum (fun k : RetainedScales J j =>  (r k.val)^(101/100:ℝ))*a^7)^50 ≤ C₀*R^249
    calc
      _  ≤  K*(((4/3:ℝ)*B*A^7)^50*R^249) := Hmul
      _ = _ := by dsimp [C₀]; ring
  obtain ⟨G,hG,hprob,hcap⟩ := posterior_spatial_cap_of_moment P Prod.fst
    (tailObservation r j) (measurable_tailObservation r j) g₀.continuous hgs hm hc hr₀ hs
    (by positivity : (0:ℝ) ≤ Z) hR hL (by positivity : 0 ≤ C₀*R^249) hmoment
  refine ⟨G,hG,?_,hcap⟩
  calc
    _  ≤  16*(64*L)^3*(C₀*R^249) := hprob
    _ = _ := by ring
end NeutralAtom
end

end

end OAI
end

theorem solution : type_of% @OAI.NeutralAtom.physical_retained_spatial_cap_oai := @OAI.NeutralAtom.physical_retained_spatial_cap_oai
