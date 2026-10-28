-- Prove2me | solution 1 for OAI.NeutralAtom.physical_observed_small_annular_count_tail
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:25:55.964592+00:00
-- url     : https://prove2.me/submissions/e3c02bdf-e59e-4e68-8f0e-b0214fce1a90

import Mathlib
import Definitions.Def_CoulombRadii
import Definitions.Def_OAIQ062C008

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

theorem measurable_rawCount {n : ℕ} {S : Set Position} (hS : MeasurableSet S) :
    Measurable (rawCount (n := n) S) := by
  apply Finset.measurable_sum
  intro i _
  exact (measurable_const.indicator hS).comp (measurable_pi_apply i)

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

lemma observationEventOffset_nonneg {H : Type*} [Fintype H] {n : ℕ}
    {ψ : Wavefunction n} {g : Gradient n} (hd : FormDomain ψ g) (hn : normSquared ψ=1)
    {D₀ : ℝ} (hD : 0 ≤ D₀) (ℓ : H → ℝ)
    {s : Set ((H × (Fin n × Fin 3)) → ℝ)} (hs : MeasurableSet s)
    (hp : 0 < stateWeightedIntegral ψ (arrayEventLikelihood ℓ s)) :
    0 ≤ D₀+observationEventEnergyConstant*observationWidthSquareSum ℓ*
      (1-Real.log (stateWeightedIntegral ψ (arrayEventLikelihood ℓ s)))^5 := by
  have h1 := stateWeightedIntegral_le_one hd hn (arrayEventLikelihood_contDiff ℓ hs).continuous.measurable
    (arrayEventLikelihood_nonneg ℓ hs) (arrayEventLikelihood_le_one ℓ hs)
  have hl := Real.log_nonpos hp.le h1
  exact add_nonneg hD (mul_nonneg (mul_nonneg observationEventEnergyConstant_pos.le
    (observationWidthSquareSum_nonneg ℓ)) (pow_nonneg (by linarith) _))

theorem atomic_arrayEvent_annular_second_moment {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {H : Type*} [Fintype H] {n : ℕ}
    (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction n} {g : Gradient n},
    FormDomain ψ g → normSquared ψ=1 →
    (∀ (χ : Wavefunction n) (h : Gradient n),
      FormDomain χ h → normSquared χ=1 → energy Z ψ g ≤ energy Z χ h) →
    ∀ {E D₀ : ℝ}, (E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E+D₀ → 0 ≤ D₀ → ∀ (ℓ : H → ℝ), (∀ h, 0 < ℓ h) →
    ∀ {s : Set ((H × (Fin n × Fin 3)) → ℝ)}, MeasurableSet s →
    (∀ (p : Equiv.Perm (Fin n)) y, permuteObservationArray p y∈s ↔ y∈s) →
    0 < stateWeightedIntegral ψ (arrayEventLikelihood ℓ s) → ∀ {r : ℝ}, 0 < r →
    (stateWeightedIntegral ψ (arrayEventLikelihood ℓ s))⁻¹ * stateWeightedIntegral ψ
      (fun x => arrayEventLikelihood ℓ s x*
        (Coulomb.localCount {z : Position | α*r < ‖z‖ ∧ ‖z‖ < β*r} (flattenConfiguration n x))^2) ≤
    C*(Coulomb.screenMass (D₀+observationEventEnergyConstant*observationWidthSquareSum ℓ*
      (1-Real.log (stateWeightedIntegral ψ (arrayEventLikelihood ℓ s)))^5) r)^2 := by
  obtain ⟨C,hC,hbound⟩ := Coulomb.atomic_annular_second_moment hα hαβ
  refine ⟨C,hC,?_⟩
  intro H _ n Z hZ ψ g hd hn hmin E D₀ hE hbase hD ℓ hℓ s hs hsym hp r hr
  obtain ⟨u,hu,hum,hue,hlaw⟩ := atomic_arrayEvent_state Z hZ hd hn hmin hbase ℓ hℓ hs hsym hp
  have hb := hbound (Coulomb.atom Z hZ) (by intro i; rfl) u hu hum hE hue
    (observationEventOffset_nonneg hd hn hD ℓ hs hp) hr
  change Coulomb.potentialForm (fun x => (Coulomb.localCount _ x)^2) u ≤ _ at hb
  rw [hlaw] at hb
  exact hb

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ConditionalMatching
attribute [-instance] _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff
namespace NeutralAtom

theorem observationNoiseVector_coordinate (v : Fin 3 → ℝ) (a : Fin 3) :
    observationNoiseVector v a = v a := by
  simp [observationNoiseVector, Pi.single_apply]

end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ObservationSmallScale
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

lemma tendsto_positive_rpow_zero {q : ℝ} (hq : 0<q) :
    Tendsto (fun r : ℝ => r^q) (𝓝[>] 0) (𝓝 0) := by
  simpa [Real.zero_rpow hq.ne'] using
    ((Real.continuous_rpow_const hq.le).tendsto 0).mono_left nhdsWithin_le_nhds

lemma singleObservationOffset_scaled_tendsto (D : ℝ) :
    Tendsto (fun r => singleObservationOffset D r*r^7) (𝓝[>] 0) (𝓝 0) := by
  have ht := (tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<249/250)).sub
    ((tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0:ℝ)<249/250)).const_mul 40)
  have hpow : Tendsto (fun r : ℝ => r^7) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0)).pow 7
  have hh := (hpow.const_mul D).add ((ht.pow 5).const_mul observationEventEnergyConstant)
  simp only [mul_zero,sub_self,zero_pow (by decide : 5≠0),add_zero] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr : 0 < r := hr
  have hpn : r^(101/100:ℝ)≠0 := (Real.rpow_pos_of_pos hr _).ne'
  have hmul : (r^(249/250:ℝ))^5*(r^(101/100:ℝ))^2=r^7 := by
    rw [←Real.rpow_natCast (r^(249/250:ℝ)) 5,←Real.rpow_mul hr.le,
      ←Real.rpow_natCast (r^(101/100:ℝ)) 2,←Real.rpow_mul hr.le,←Real.rpow_add hr]
    norm_num
  have hratio : ((r^(101/100:ℝ))⁻¹)^2*r^7=(r^(249/250:ℝ))^5 := by
    rw [←hmul]
    field_simp
  dsimp [singleObservationOffset]
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  calc
    D*r^7+observationEventEnergyConstant*(r^(249/250:ℝ)-40*(Real.log r*r^(249/250:ℝ)))^5 =
      D*r^7+observationEventEnergyConstant*(r^(249/250:ℝ))^5*(1-40*Real.log r)^5 := by ring
    _ = _ := by rw [←hratio]; ring

lemma screenMass_small_offset {D r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hD : 0 ≤ D) (hsmall : D*r^7 ≤ 1) :
    Coulomb.screenMass D r ≤ 2/r^3 := by
  have hr3 : 0 < r^3 := pow_pos hr _
  have hb : Coulomb.screenBaseMass r=(r^3)⁻¹ := by
    unfold Coulomb.screenBaseMass
    apply max_eq_left
    exact (one_le_inv₀ hr3).mpr (pow_le_one₀ hr.le hr1)
  have hs : Real.sqrt (D*r) ≤ (r^3)⁻¹ := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (inv_nonneg.mpr hr3.le)).mp
    rw [Real.sq_sqrt (mul_nonneg hD hr.le), inv_pow, inv_eq_one_div,
      le_div_iff₀ (pow_pos hr3 _)]
    nlinarith [hsmall]
  unfold Coulomb.screenMass
  rw [hb]
  calc
    (r^3)⁻¹+Real.sqrt (D*r) ≤ (r^3)⁻¹+(r^3)⁻¹ := add_le_add le_rfl hs
    _ = 2/r^3 := by ring

lemma observation_displacement_ratio_tendsto :
    Tendsto (fun r : ℝ => Real.sqrt 3*r^(101/100:ℝ)/r) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<1/100)).const_mul (Real.sqrt 3)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr : 0 < r := hr
  have hx : r^(101/100:ℝ)/r=r^((101/100:ℝ)-1) := by rw [Real.rpow_sub hr,Real.rpow_one]
  rw [mul_div_assoc,hx]
  norm_num

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

lemma observationProductDensity_ne_zero_support {I : Type*} [Fintype I]
    {u : I → ℝ} (hu : observationProductDensity u≠0) (i : I) : |u i|<1 := by
  have hi : observationNoiseDensity (u i)≠0 := fun h => hu (Finset.prod_eq_zero (Finset.mem_univ i) h)
  by_contra h
  apply hi
  rw [observationNoiseDensity_formula,ite_eq_right h,mul_zero]

lemma arrayEventLikelihood_pos_matching {H : Type*} [Fintype H] {n : ℕ}
    (ℓ : H → ℝ) (hℓ : ∀ h, ℓ h≠0)
    (s : Set ((H × (Fin n × Fin 3)) → ℝ)) (x : Configuration n)
    (hp : 0 < arrayEventLikelihood ℓ s x) :
    ∃ u : (H × (Fin n × Fin 3)) → ℝ, (∀ ia, |u ia|<1) ∧
      (fun ia => x ia.2.1 ia.2.2+ℓ ia.1*u ia)∈s := by
  by_contra hn
  push Not at hn
  have he : arrayEventLikelihood ℓ s x=0 := by
    rw [arrayEventLikelihood_integral ℓ hℓ,observationNoiseLaw_pi_integral]
    apply integral_eq_zero_of_ae
    filter_upwards [] with u
    by_cases hu : observationProductDensity u=0
    · simp [hu]
    · simp [Set.indicator_of_notMem (hn u (observationProductDensity_ne_zero_support hu))]
  linarith

lemma observationArrayPositions_displacement {H : Type*} {n : ℕ}
    (ℓ : H → ℝ) (hℓ : ∀ h, 0<ℓ h) (x : Configuration n)
    {u : (H × (Fin n × Fin 3)) → ℝ} (hu : ∀ ia, |u ia|<1) (h : H) (i : Fin n) :
    ‖observationArrayPositions h (fun ia => x ia.2.1 ia.2.2+ℓ ia.1*u ia) i-x i‖ ≤
      Real.sqrt 3*ℓ h := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (hℓ h).le)).mp
  rw [EuclideanSpace.real_norm_sq_eq,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  calc
    _ = ∑ a : Fin 3, (ℓ h*u (h,i,a))^2 := by
      apply Finset.sum_congr rfl
      intro a _
      change (x i a+ℓ h*u (h,i,a)-x i a)^2=_
      ring
    _ ≤ ∑ _a : Fin 3, (ℓ h)^2 := Finset.sum_le_sum (fun a _ => by
      have H := (sq_le_sq₀ (abs_nonneg (u (h,i,a))) (by norm_num : (0:ℝ)≤1)).2 (hu (h,i,a)).le
      rw [sq_abs,one_pow] at H
      nlinarith [mul_le_mul_of_nonneg_left H (sq_nonneg (ℓ h))])
    _ = _ := by simp

lemma observed_annular_count_le {n : ℕ} (x y : Configuration n)
    {a b A B d : ℝ} (hd : ∀ i, ‖y i-x i‖≤d)
    (hA : A+d<a) (hB : b+d<B) :
    rawCount {z : Position | a≤‖z‖ ∧ ‖z‖≤b} y ≤
      Coulomb.localCount {z : Position | A<‖z‖ ∧ ‖z‖<B} (flattenConfiguration n x) := by
  unfold rawCount Coulomb.localCount
  apply Finset.sum_le_sum
  intro i _
  simp only [position_flattenConfiguration]
  by_cases hi : a≤‖y i‖ ∧ ‖y i‖≤b
  · have hx : A<‖x i‖ ∧ ‖x i‖<B := by
      have h1 := norm_le_norm_add_norm_sub (y i) (x i)
      have h2 := norm_le_norm_add_norm_sub (x i) (y i)
      rw [norm_sub_rev (x i) (y i)] at h2
      constructor <;> linarith [hd i]
    simp [hi,hx]
  · simpa [Set.indicator, hi] using
      (Set.indicator_nonneg (s:={z : Position | A<‖z‖ ∧ ‖z‖<B}) (fun _ _ => (zero_le_one : (0:ℝ)≤1)) (x i))

lemma observed_annular_event_implies_raw_count {H : Type*} [Fintype H] {n : ℕ}
    (ℓ : H → ℝ) (hℓ : ∀ h, 0<ℓ h) (h : H)
    {a b A B T : ℝ} (hA : A+Real.sqrt 3*ℓ h<a) (hB : b+Real.sqrt 3*ℓ h<B)
    (x : Configuration n)
    (hp : 0<arrayEventLikelihood ℓ
      {y | T < rawCount {z : Position | a≤‖z‖ ∧ ‖z‖≤b} (observationArrayPositions h y)} x) :
    T<Coulomb.localCount {z : Position | A<‖z‖ ∧ ‖z‖<B} (flattenConfiguration n x) := by
  obtain ⟨u,hu,hs⟩ := arrayEventLikelihood_pos_matching ℓ (fun h => (hℓ h).ne') _ x hp
  exact hs.trans_le (observed_annular_count_le x _
    (fun i => observationArrayPositions_displacement ℓ hℓ x hu h i) hA hB)

lemma measurable_observationArrayPositions {H : Type*} {n : ℕ} (h : H) :
    Measurable (@observationArrayPositions H n h) := by
  unfold observationArrayPositions
  fun_prop

lemma observed_annular_event_measurable {H : Type*} {n : ℕ} (h : H) (a b T : ℝ) :
    MeasurableSet {y : (H × (Fin n × Fin 3)) → ℝ |
      T < rawCount {z : Position | a≤‖z‖ ∧ ‖z‖≤b} (observationArrayPositions h y)} := by
  exact measurableSet_lt measurable_const ((measurable_rawCount
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)).measurableSet).comp (measurable_observationArrayPositions h))

lemma observed_annular_event_symmetric {H : Type*} {n : ℕ} (h : H) (a b T : ℝ)
    (p : Equiv.Perm (Fin n)) (y : (H × (Fin n × Fin 3)) → ℝ) :
    permuteObservationArray p y∈{y | T < rawCount {z : Position | a≤‖z‖ ∧ ‖z‖≤b} (observationArrayPositions h y)} ↔
      y∈{y | T < rawCount {z : Position | a≤‖z‖ ∧ ‖z‖≤b} (observationArrayPositions h y)} := by
  have he : observationArrayPositions h (permuteObservationArray p y)=observationArrayPositions h y ∘ p := rfl
  simp only [Set.mem_ofPred_eq,he,rawCount,Function.comp_apply]
  have hh := Equiv.sum_comp p (fun i => {z : Position | a≤‖z‖ ∧ ‖z‖≤b}.indicator (fun _ => (1:ℝ)) (observationArrayPositions h y i))
  exact congrArg (fun q => T<q) hh |> Iff.of_eq
end NeutralAtom

end
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
namespace NeutralAtom

lemma stateWeightedIntegral_mono_bounded {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) {F G : Configuration n → ℝ}
    (hF : Measurable F) (hG : Measurable G)
    {C D : ℝ} (hFb : ∀ x, |F x| ≤ C) (hGb : ∀ x, |G x| ≤ D) (hFG : ∀ x, F x ≤ G x) :
    stateWeightedIntegral ψ F ≤ stateWeightedIntegral ψ G := by
  unfold stateWeightedIntegral
  apply Finset.sum_le_sum
  intro σ _
  exact integral_mono (stateWeighted_integrable hd hF hFb σ) (stateWeighted_integrable hd hG hGb σ)
    (fun x => mul_le_mul_of_nonneg_right (hFG x) (sq_nonneg _))

lemma stateWeightedIntegral_const_mul {n : ℕ} (ψ : Wavefunction n)
    (F : Configuration n → ℝ) (c : ℝ) :
    stateWeightedIntegral ψ (fun x => c*F x)=c*stateWeightedIntegral ψ F := by
  unfold stateWeightedIntegral
  simp_rw [mul_assoc,integral_const_mul,Finset.mul_sum]

lemma event_count_square_lower {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) {F : Configuration n → ℝ} (hF : Measurable F)
    (hF0 : ∀ x, 0 ≤ F x) (hF1 : ∀ x, F x ≤ 1)
    {A : Set Position} (hA : MeasurableSet A) {T : ℝ} (hT : 0 ≤ T)
    (hmatch : ∀ x, 0<F x → T ≤ Coulomb.localCount A (flattenConfiguration n x))
    (hp : 0 < stateWeightedIntegral ψ F) :
    T^2 ≤ (stateWeightedIntegral ψ F)⁻¹*stateWeightedIntegral ψ
      (fun x => F x*(Coulomb.localCount A (flattenConfiguration n x))^2) := by
  have hcm : Measurable (fun x : Configuration n => Coulomb.localCount A (flattenConfiguration n x)) :=
    (Coulomb.localCount_measurable hA).comp (flattenConfiguration n).continuous.measurable
  have H := stateWeightedIntegral_mono_bounded hd
    (F:=fun x => T^2*F x) (G:=fun x => F x*(Coulomb.localCount A (flattenConfiguration n x))^2)
    (measurable_const.mul hF)
    (hF.mul (hcm.pow_const 2)) (C:=T^2) (D:=(n:ℝ)^2)
    (fun x => by rw [abs_mul,abs_of_nonneg (sq_nonneg _),abs_of_nonneg (hF0 x)]; exact mul_le_of_le_one_right (sq_nonneg _) (hF1 x))
    (fun x => by
      rw [abs_of_nonneg (mul_nonneg (hF0 x) (sq_nonneg _))]
      exact (mul_le_of_le_one_left (sq_nonneg _) (hF1 x)).trans
        (pow_le_pow_left₀ (Coulomb.localCount_nonneg A _) (Coulomb.localCount_le A _) 2))
    (fun x => by
      by_cases hx : F x=0
      · simp [hx]
      · have H2 := pow_le_pow_left₀ hT (hmatch x (lt_of_le_of_ne (hF0 x) (Ne.symm hx))) 2
        nlinarith [mul_le_mul_of_nonneg_left H2 (hF0 x)])
  rw [stateWeightedIntegral_const_mul] at H
  calc
    T^2=(stateWeightedIntegral ψ F)⁻¹*(T^2*stateWeightedIntegral ψ F) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left H (inv_nonneg.mpr hp.le)

lemma observationEventOffset_mono_probability {H : Type*} [Fintype H]
    (ℓ : H → ℝ) (D : ℝ) {p q : ℝ} (hp : 0<p) (hpq : p ≤ q) (hq : q ≤ 1) :
    D+observationEventEnergyConstant*observationWidthSquareSum ℓ*(1-Real.log q)^5  ≤
    D+observationEventEnergyConstant*observationWidthSquareSum ℓ*(1-Real.log p)^5 := by
  have hlog := Real.log_le_log hp hpq
  have hlog0 := Real.log_nonpos ((hp.trans_le hpq).le) hq
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by linarith) (by linarith) 5)
    (mul_nonneg observationEventEnergyConstant_pos.le (observationWidthSquareSum_nonneg ℓ)))

theorem atomic_observed_annular_count_tail {α β : ℝ} (hα : 0<α) (hαβ : α<β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {H : Type*} [Fintype H] {n : ℕ}
    (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction n} {g : Gradient n},
    FormDomain ψ g → normSquared ψ=1 →
    (∀ (χ : Wavefunction n) (h : Gradient n), FormDomain χ h → normSquared χ=1 → energy Z ψ g ≤ energy Z χ h) →
    ∀ {E D₀ : ℝ}, (E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E+D₀ → 0 ≤ D₀ → ∀ (ℓ : H → ℝ), (∀ h,0<ℓ h) →
    ∀ (h : H) {r a b T p₀ : ℝ}, 0 < r → 0 ≤ T → 0<p₀ →
    α*r+Real.sqrt 3*ℓ h<a → b+Real.sqrt 3*ℓ h<β*r →
    C*(Coulomb.screenMass (D₀+observationEventEnergyConstant*observationWidthSquareSum ℓ*
      (1-Real.log p₀)^5) r)^2<T^2 →
    stateWeightedIntegral ψ (arrayEventLikelihood ℓ
      {y | T < rawCount {z : Position | a ≤ ‖z‖ ∧ ‖z‖ ≤ b} (observationArrayPositions h y)}) ≤ p₀ := by
  obtain ⟨C,hC,hbound⟩ := atomic_arrayEvent_annular_second_moment hα hαβ
  refine ⟨C,hC,?_⟩
  intro H _ n Z hZ ψ g hd hn hmin E D₀ hE hbase hD ℓ hℓ h r a b T p₀ hr hT hp₀ hA hB hth
  let s : Set ((H × (Fin n × Fin 3)) → ℝ) := {y | T < rawCount {z : Position | a ≤ ‖z‖ ∧ ‖z‖ ≤ b} (observationArrayPositions h y)}
  have hs : MeasurableSet s := observed_annular_event_measurable h a b T
  by_contra hc
  have hp : 0 < stateWeightedIntegral ψ (arrayEventLikelihood ℓ s) := hp₀.trans (lt_of_not_ge hc)
  have hp1 := stateWeightedIntegral_le_one hd hn (arrayEventLikelihood_contDiff ℓ hs).continuous.measurable
    (arrayEventLikelihood_nonneg ℓ hs) (arrayEventLikelihood_le_one ℓ hs)
  have hlow := event_count_square_lower hd (arrayEventLikelihood_contDiff ℓ hs).continuous.measurable
    (arrayEventLikelihood_nonneg ℓ hs) (arrayEventLikelihood_le_one ℓ hs)
    ((isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)).measurableSet hT
    (fun x hx => (observed_annular_event_implies_raw_count ℓ hℓ h hA hB x hx).le) hp
  have hu := hbound Z hZ hd hn hmin hE hbase hD ℓ hℓ hs
    (observed_annular_event_symmetric h a b T) hp hr
  have hδ := observationEventOffset_mono_probability ℓ D₀ hp₀ (le_of_not_ge hc) hp1
  have hmass : Coulomb.screenMass (D₀+observationEventEnergyConstant*observationWidthSquareSum ℓ*
      (1-Real.log (stateWeightedIntegral ψ (arrayEventLikelihood ℓ s)))^5) r  ≤
    Coulomb.screenMass (D₀+observationEventEnergyConstant*observationWidthSquareSum ℓ*(1-Real.log p₀)^5) r := by
    unfold Coulomb.screenMass
    exact add_le_add le_rfl (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hδ hr.le))
  exact (not_lt_of_ge (hlow.trans (hu.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Coulomb.screenMass_pos _ _).le hmass 2) hC)))) hth
end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PhysicalLikelihoodBridge
attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
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

lemma flattenObservationNoise_preserving (n J : ℕ) :
    MeasurePreserving (flattenObservationNoise n J) (allObservationNoiseLaw n J)
      (Measure.pi (fun _ : Fin J × (Fin n × Fin 3) => observationNoiseLaw)) := by
  refine ⟨(flattenObservationNoise n J).measurable,?_⟩
  refine (Measure.pi_eq (fun v hv => ?_)).symm
  rw [MeasurableEquiv.map_apply]
  have he : (flattenObservationNoise n J) ⁻¹' Set.univ.pi v=
      Set.univ.pi (fun j => Set.univ.pi (fun i => Set.univ.pi (fun a => v (j,i,a)))) := by
    ext u
    simp only [mem_preimage,Set.mem_pi,mem_univ,true_implies,flattenObservationNoise,
      MeasurableEquiv.coe_mk,Equiv.coe_fn_mk]
    exact ⟨fun h j i a => h (j,i,a),fun h ⟨j,i,a⟩ => h j i a⟩
  rw [he]
  simp only [allObservationNoiseLaw,Measure.pi_pi]
  simp only [Fintype.prod_prod_type]

lemma measurable_observationCoordinateData {n J : ℕ} (ℓ : Fin J → ℝ) :
    Measurable (@observationCoordinateData n J ℓ) := by
  unfold observationCoordinateData
  fun_prop

lemma arrayEventLikelihood_nested_integral {n J : ℕ} (ℓ : Fin J → ℝ)
    (hℓ : ∀ h, ℓ h≠0) (B : Set ((Fin J × (Fin n × Fin 3)) → ℝ))
    (x : Configuration n) :
    arrayEventLikelihood ℓ B x=
      ∫ u, B.indicator (fun _ => (1:ℝ)) (observationCoordinateData ℓ (x,u))
        ∂allObservationNoiseLaw n J := by
  rw [arrayEventLikelihood_integral ℓ hℓ]
  exact ((flattenObservationNoise_preserving n J).integral_comp'
    (fun u => B.indicator (fun _ => (1:ℝ)) (fun ia => x ia.2.1 ia.2.2+ℓ ia.1*u ia))).symm

lemma rawExpectation_eq_stateWeightedIntegral {n : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) {F : Configuration n → ℝ}
    (hF : Measurable F) {C : ℝ} (hC : ∀ x, ‖F x‖≤C) :
    rawExpectation ψ F=stateWeightedIntegral ψ F := by
  unfold rawExpectation configurationDensity stateWeightedIntegral
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum _ (fun σ _ =>
    (hψ σ).norm.integrable_sq.bdd_mul hF.aestronglyMeasurable
      (Eventually.of_forall hC))

theorem physical_arrayEvent_bayes_integral {n J : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hn : normSquared ψ=1)
    (ℓ : Fin J → ℝ) (hℓ : ∀ h, ℓ h≠0)
    {B : Set ((Fin J × (Fin n × Fin 3)) → ℝ)} (hB : MeasurableSet B)
    {F : Configuration n → ℝ} (hF : Measurable F) {C : ℝ}
    (hC : ∀ x, ‖F x‖≤C) :
    (∫ sample, ((observationCoordinateData ℓ) ⁻¹' B).indicator
      (fun z => F z.1) sample ∂observationLaw J (rawLaw ψ))=
    stateWeightedIntegral ψ (fun x => arrayEventLikelihood ℓ B x*F x) := by
  let := rawLaw_isProbability hψ hn
  have hi : Integrable (fun z : ObservationSample n J => F z.1)
      (observationLaw J (rawLaw ψ)) :=
    (integrable_const C).mono' (hF.comp measurable_fst).aestronglyMeasurable
      (Eventually.of_forall (fun z => hC z.1))
  have hA := hB.preimage (measurable_observationCoordinateData ℓ)
  rw [observationLaw,integral_prod _ (hi.indicator hA)]
  have hi2 : (fun x : Configuration n => ∫ u,
      ((observationCoordinateData ℓ) ⁻¹' B).indicator (fun z => F z.1) (x,u)
        ∂allObservationNoiseLaw n J)=
      fun x => arrayEventLikelihood ℓ B x*F x := by
    funext x
    rw [arrayEventLikelihood_nested_integral ℓ hℓ B x,←integral_mul_const]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by
      by_cases h : observationCoordinateData ℓ (x,u)∈B <;> simp [h]
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

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ObservationAnnulusTail
attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
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

theorem atomic_observed_small_annular_count_tail {α A B β : ℝ}
    (hα : 0<α) (hαA : α<A) (hAB : A<B) (hBβ : B<β) :
    ∃ K : ℝ, 0<K ∧ ∀ D₀ : ℝ, 0 ≤ D₀ → ∃ s : ℝ, 0 < s ∧
    ∀ {n : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction n} {g : Gradient n},
    FormDomain ψ g → normSquared ψ=1 →
    (∀ (χ : Wavefunction n) (h : Gradient n), FormDomain χ h → normSquared χ=1 → energy Z ψ g ≤ energy Z χ h) →
    ∀ {E : ℝ}, (E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E+D₀ → ∀ {r : ℝ}, 0 < r → r < s →
    stateWeightedIntegral ψ (arrayEventLikelihood (fun _ : Fin 1 => r^(101/100:ℝ))
      {y | K/r^3 < rawCount {z : Position | A*r ≤ ‖z‖ ∧ ‖z‖ ≤ B*r} (observationArrayPositions 0 y)}) ≤ r^40 := by
  obtain ⟨C,hC,hbound⟩ := atomic_observed_annular_count_tail hα (by linarith : α<β)
  let K := 2*Real.sqrt C+1
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  intro D₀ hD
  have hevent : ∀ᶠ r : ℝ in 𝓝[>] 0, r<1 ∧ singleObservationOffset D₀ r*r^7 ≤ 1 ∧
      Real.sqrt 3*r^(101/100:ℝ)/r<A-α ∧ Real.sqrt 3*r^(101/100:ℝ)/r<β-B := by
    have hm := (singleObservationOffset_scaled_tendsto D₀).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
    have ha := observation_displacement_ratio_tendsto.eventually (gt_mem_nhds (by linarith : 0<A-α))
    have hb := observation_displacement_ratio_tendsto.eventually (gt_mem_nhds (by linarith : 0<β-B))
    have hr : ∀ᶠ r : ℝ in 𝓝[>] 0, r<1 :=
      (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hr,hm,ha,hb] with r hr hm ha hb
    exact ⟨hr,hm.le,ha,hb⟩
  obtain ⟨s,hs,hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp hevent
  refine ⟨s,hs,?_⟩
  intro n Z hZ ψ g hd hn hmin E hE hbase r hr hrs
  obtain ⟨hr1,hm,ha,hb⟩ := hsub ⟨hr,hrs⟩
  have hδ : 0 ≤ singleObservationOffset D₀ r := by
    unfold singleObservationOffset
    have hl : Real.log (r^40) ≤ 0 := Real.log_nonpos (by positivity) (pow_le_one₀ hr.le hr1.le)
    exact add_nonneg hD (mul_nonneg (mul_nonneg observationEventEnergyConstant_pos.le
      (sq_nonneg _)) (pow_nonneg (by linarith) _))
  have hmass := screenMass_small_offset hr hr1.le hδ hm
  have hcoeff : 4*C<K^2 := by
    dsimp [K]
    nlinarith [Real.sq_sqrt hC,Real.sqrt_nonneg C]
  have hth : C*(Coulomb.screenMass (singleObservationOffset D₀ r) r)^2<(K/r^3)^2 := by
    calc
      _ ≤ C*(2/r^3)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Coulomb.screenMass_pos _ _).le hmass 2) hC
      _ < (K/r^3)^2 := by
        rw [div_pow,div_pow,←mul_div_assoc]
        exact (div_lt_div_iff_of_pos_right (pow_pos (pow_pos hr _) _)).mpr (by nlinarith)
  have ha' : α*r+Real.sqrt 3*r^(101/100:ℝ)<A*r := by
    have := (div_lt_iff₀ hr).mp ha
    nlinarith
  have hb' : B*r+Real.sqrt 3*r^(101/100:ℝ)<β*r := by
    have := (div_lt_iff₀ hr).mp hb
    nlinarith
  have hsum : observationWidthSquareSum (fun _ : Fin 1 => r^(101/100:ℝ))=((r^(101/100:ℝ))⁻¹)^2 := by
    simp [observationWidthSquareSum]
  have ht' : C*(Coulomb.screenMass (D₀+observationEventEnergyConstant*
      observationWidthSquareSum (fun _ : Fin 1 => r^(101/100:ℝ))*(1-Real.log (r^40))^5) r)^2<(K/r^3)^2 := by
    simpa only [hsum,singleObservationOffset] using hth
  exact hbound Z hZ hd hn hmin hE hbase hD _
    (fun _ => Real.rpow_pos_of_pos hr _) (0:Fin 1) hr (by positivity) (by positivity) ha' hb' ht'
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace NeutralAtom

lemma observationSingleScale_preserving {n J : ℕ}
    (ν : Measure (Configuration n)) [SFinite ν] (k : Fin J) :
    MeasurePreserving (observationSingleScale k) (observationLaw J ν) (observationLaw 1 ν) := by
  have hn : MeasurePreserving (fun u : ObservationNoise n J => fun _ : Fin 1 => u k)
      (allObservationNoiseLaw n J) (allObservationNoiseLaw n 1) :=
    (measurePreserving_funUnique
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin 3 => observationNoiseLaw)))
      (Fin 1)).symm.comp (measurePreserving_eval _ k)
  exact (MeasurePreserving.id ν).prod hn

lemma physical_arrayEvent_probability {n J : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hn : normSquared ψ=1)
    (ℓ : Fin J → ℝ) (hℓ : ∀ k, ℓ k≠0)
    {B : Set ((Fin J × (Fin n × Fin 3)) → ℝ)} (hB : MeasurableSet B) :
    (observationLaw J (rawLaw ψ)).real (observationCoordinateData ℓ ⁻¹' B)=
      stateWeightedIntegral ψ (arrayEventLikelihood ℓ B) := by
  have H := physical_arrayEvent_bayes_integral hψ hn ℓ hℓ hB
    (measurable_const : Measurable (fun _ : Configuration n => (1:ℝ)))
    (C:=1) (fun _ => by simp)
  simpa only [integral_indicator_const _ (hB.preimage (measurable_observationCoordinateData ℓ)),
    smul_eq_mul,mul_one] using H

theorem physical_observed_small_annular_count_tail_oai {α A B β : ℝ}
    (hα : 0<α) (hαA : α<A) (hAB : A<B) (hBβ : B<β) :
    ∃ K : ℝ, 0<K ∧ ∀ D₀ : ℝ, 0≤D₀ → ∃ s : ℝ, 0 < s ∧
    ∀ {n J : ℕ} (Z : ℕ) (hZ : 1≤Z) {ψ : Wavefunction n} {g : Gradient n},
    FormDomain ψ g → normSquared ψ=1 →
    (∀ (χ : Wavefunction n) (h : Gradient n), FormDomain χ h → normSquared χ=1 → energy Z ψ g≤energy Z χ h) →
    ∀ {E : ℝ}, (E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g≤E+D₀ → ∀ (r : Fin J → ℝ) (k : Fin J), 0 < r k → r k < s →
    (observationLaw J (rawLaw ψ)).real
      {sample | K/(r k)^3 < rawCount {z : Position | A*r k≤‖z‖ ∧ ‖z‖≤B*r k}
        (observedOrdered r k sample)}≤(r k)^40 := by
  obtain ⟨K,hK,H⟩ := atomic_observed_small_annular_count_tail hα hαA hAB hBβ
  refine ⟨K,hK,?_⟩
  intro D₀ hD
  obtain ⟨s,hs,Hs⟩ := H D₀ hD
  refine ⟨s,hs,?_⟩
  intro n J Z hZ ψ g hd hn hmin E hE hbase r k hr hrs
  have := rawLaw_isProbability hd.2.2.1 hn
  let S : Set ((Fin 1 × (Fin n × Fin 3)) → ℝ) :=
    {y | K/(r k)^3 < rawCount {z : Position | A*r k≤‖z‖ ∧ ‖z‖≤B*r k}
      (observationArrayPositions 0 y)}
  have hS : MeasurableSet S := observed_annular_event_measurable _ _ _ _
  have hp := physical_arrayEvent_probability hd.2.2.1 hn
    (fun _ : Fin 1 => (r k)^(101/100:ℝ)) (fun _ => (Real.rpow_pos_of_pos hr _).ne') hS
  have hpre : observationSingleScale k ⁻¹'
      (observationCoordinateData (fun _ : Fin 1 => (r k)^(101/100:ℝ)) ⁻¹' S)=
      {sample | K/(r k)^3 < rawCount {z : Position | A*r k≤‖z‖ ∧ ‖z‖≤B*r k}
        (observedOrdered r k sample)} := by
    ext sample
    have he : observationArrayPositions (0:Fin 1)
        (observationCoordinateData (fun _ : Fin 1 => (r k)^(101/100:ℝ))
          (observationSingleScale k sample))=observedOrdered r k sample := by
      funext i
      ext a
      simp [observationArrayPositions,observationCoordinateData,observationSingleScale,
        observedOrdered,observationNoiseVector_coordinate]
    simp only [mem_preimage,S,mem_ofPred_eq,he]
  rw [←hpre]
  have he := (observationSingleScale_preserving (rawLaw ψ) k).measure_preimage
    (hS.preimage (measurable_observationCoordinateData
      (fun _ : Fin 1 => (r k)^(101/100:ℝ)))).nullMeasurableSet
  unfold Measure.real
  rw [he]
  change (observationLaw 1 (rawLaw ψ)).real _≤_
  rw [hp]
  exact Hs Z hZ hd hn hmin hE hbase hr hrs
end NeutralAtom
end

end
end

end OAI
end

theorem solution : type_of% @OAI.NeutralAtom.physical_observed_small_annular_count_tail_oai := @OAI.NeutralAtom.physical_observed_small_annular_count_tail_oai
