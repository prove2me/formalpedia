-- Prove2me | solution 1 for OAI.NeutralAtom.physical_retained_master_fresh_transfer
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:36:23.022229+00:00
-- url     : https://prove2.me/submissions/1e2a5fa9-74cf-4268-b94a-7751acd946c9

import Mathlib
import Definitions.Def_CoulombRadii
import Definitions.Def_OAIQ062C008
import Theorems.Thm_OAI_Coulomb_exists_atomic_near_scale

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

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_NuclearPotentialSplitJoin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
namespace Coulomb

lemma conditional_core_nuclear_identity {M m k : ℕ} (S : Nuclei M) (ψ : H1Vector (m+k)) :
    (∑ s : Spins m, ∫ x, mass (ψ.coreSlice s x) * nuclearEnergy S (ψ.coreSlice s x).normalized) =
      ∑ st : Spins (m+k), ∫ z, nuclearPotential S ((joinConfiguration m k).symm z).2 * ‖ψ.value st z‖^2 := by
  change (∑ s : Spins m, ∫ x, mass (ψ.coreSlice s x) *
    potentialForm (nuclearPotential S) (ψ.coreSlice s x).normalized) = _
  simp_rw [potentialForm_normalized_weight]
  exact integral_potentialForm_coreSlice ψ (nuclearPotential S) (ψ.core_nuclear_integrable S)

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TfFunctionalUniformBound
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
lemma tfBregman_nonneg {f g : TFLp μ} (hf : TFNonneg f) (hg : TFNonneg g) :
    0 ≤ tfBregman f g := by
  rw [tfBregman_formula hf hg]
  apply integral_nonneg_of_ae
  filter_upwards [hf,hg] with x hx hy
  exact tf_power_tangent hx hy
variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]
lemma tfEnergy_minimizer_expansion {c : ℝ} (hc : 0 < c) (W : TFLq (volume.restrict Ω))
    {f g : TFLp (volume.restrict Ω)} (hf : TFNonneg f)
    (hm : ∀ h, TFNonneg h → tfEnergy hΩ c W f ≤ tfEnergy hΩ c W h) :
    tfEnergy hΩ c W g-tfEnergy hΩ c W f =
      tfCoulomb Ω (g-f) (g-f)/2+c*tfBregman f g+
        ∫ x in Ω, max (tfPotential f x-W x) 0*g x := by
  rw [tfEnergy_expansion hΩ c W hf,map_sub,tfGradientField_self hΩ c W hf hm,sub_zero,
    tfFieldContinuous_apply]
  congr 1
  apply integral_congr_ae
  filter_upwards [tfEuler_equation hΩ hc W hf hm] with x hx
  rw [hx.2]
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PhysicalEnsembleGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace Coulomb

theorem physical_ensemble_gap {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n)
    (T : RecordedEnsemble n) (_ : T.Conserves ψ) (hc : T.CoreFermionic) (ho : T.OutFermionic)
    (hm : T.totalMass=1) {E B : ℝ} (hE : (E:EReal)≤unrestrictedFormBottom S)
    (henergy : T.totalForm S≤E+B)
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a) (ht : t∈Set.Icc (5*a) (6*a))
    (y : Space) (hn : ∀ j, 20*a≤‖S.position j-y‖)
    (hcs : T.CoreSupported {z | t≤‖z-y‖}) (hos : T.OutSupported (Metric.closedBall y (t+b)))
    (F : (p : T.index) → Spins (T.out p) → Configuration (T.out p) → ℝ)
    (hFm : ∀ p s, AEStronglyMeasurable (F p s) volume)
    (hF0 : ∀ p s, ∀ᵐ x, 0≤F p s x)
    (hFi : ∀ p s, Integrable (fun x => mass ((T.vector p).coreSlice s x)*(F p s x)^2))
    (hcap : ∀ p s, ∀ᵐ x, ∀ w∈Metric.closedBall y (t+b), coreScreenedField S ((T.vector p).coreSlice s x).normalized w≤F p s x) :
    let Q := ∑ p, sliceExpectation (T.vector p) (fun s x => (F p s x)^2)
    let N := ∑ p, (T.out p:ℝ)^2*mass (T.vector p)
    let ρ := fun p s x => localTFDensity measurableSet_ball
      (coreTFField S ((T.vector p).coreSlice s x).normalized measurableSet_ball ha
        (patch_nucleus_separation S ha hb ht.2 y hn))
    (∑ p, sliceExpectation (T.vector p) (fun s x =>
      rawThomasFermiEnergy (coreScreenedField S ((T.vector p).coreSlice s x).normalized)
        (retainedFineDensity b (patchRetained y t b x) (position x))-
      rawThomasFermiEnergy (coreScreenedField S ((T.vector p).coreSlice s x).normalized) (ρ p s x))) ≤
    B+12*a*unitWindowKinetic/b^2*Real.sqrt Q+Real.sqrt (Q*T.deletedSquare y t b)+
      (b⁻¹)^2*((Real.pi^2/2)*neumannBoundary)*N^(2/3:ℝ)+
      ((2*Real.pi+1)/(2*b))*Real.sqrt N := by
  dsimp only
  let ρ := fun p s x => localTFDensity measurableSet_ball
    (coreTFField S ((T.vector p).coreSlice s x).normalized measurableSet_ball ha
      (patch_nucleus_separation S ha hb ht.2 y hn))
  let G := fun p s x => rawThomasFermiEnergy (coreScreenedField S ((T.vector p).coreSlice s x).normalized)
    (retainedFineDensity b (patchRetained y t b x) (position x))-
    rawThomasFermiEnergy (coreScreenedField S ((T.vector p).coreSlice s x).normalized) (ρ p s x)
  have hcs' (p : T.index) (s) : ∀ᵐ x, SpatiallySupported ((T.vector p).coreSlice s x).normalized {z | t≤‖z-y‖} := by
    filter_upwards [(hcs p).coreSlice s] with x hx
    exact hx.normalized
  have hcap' (p : T.index) (s) : ∀ᵐ x, ∀ w∈Metric.ball y (t-4*b), coreScreenedField S ((T.vector p).coreSlice s x).normalized w≤F p s x := by
    filter_upwards [hcap p s] with x hx
    exact fun w hw => hx w (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith)) hw)
  have hgap (p : T.index) := physical_patch_comparison S (T.vector p) (ho p).outer_symmetry
    (fun s => (hc p).coreSlice s) ha hb hsmall ht y hn (hcs' p) (fun s => (hos p).recorded_positions s)
    (F p) (hFm p) (hF0 p) (hFi p) (hcap p) hE
  have hpacket (p : T.index) := patch_packet_expected_bound S (T.vector p) ha hb ht.2 y hn
    (F p) (hFm p) (hF0 p) (hFi p) (hcap' p)
  have hmean := slice_ensemble_mean_le_sqrt T.out T.core T.vector F hFm hF0 hFi hm
  have hdel := slice_ensemble_mul_le_sqrt T.out T.core T.vector F
    (fun _ _ x => localCount {z | t-7*b≤‖z-y‖} x) hFi
    (fun p s => sliceCount_weight_integrable (T.vector p) (isClosed_le continuous_const (by fun_prop)).measurableSet s 2)
    (fun p s => weighted_cap_count_integrable (mass_coreSlice_integrable (T.vector p) s)
      (Eventually.of_forall (fun _ => mass_nonneg _)) (hFm p s) (hF0 p s) (hFi p s)
      (localCount_measurable (isClosed_le continuous_const (by fun_prop)).measurableSet).aestronglyMeasurable
      (Nat.cast_nonneg (T.out p)) (Eventually.of_forall (fun x => ⟨localCount_nonneg _ x,localCount_le _ x⟩)))
  have hfine := ensemble_fineLocalizationError T.out (fun p => mass (T.vector p)) (fun p => mass_nonneg _) hm hb
  have hsumgap := Finset.sum_le_sum (fun p (_ : p∈Finset.univ) => hgap p)
  have hsumpacket := Finset.sum_le_sum (fun p (_ : p∈Finset.univ) => hpacket p)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum] at hsumgap hsumpacket
  change (∑ p, sliceExpectation (T.vector p) (G p))≤_ at hsumgap
  have hGapBound : (∑ p, sliceExpectation (T.vector p) (G p))≤B+
      12*a*unitWindowKinetic/b^2*Real.sqrt (∑ p, sliceExpectation (T.vector p) (fun s x => (F p s x)^2))+
      Real.sqrt ((∑ p, sliceExpectation (T.vector p) (fun s x => (F p s x)^2))*T.deletedSquare y t b)+
      (b⁻¹)^2*((Real.pi^2/2)*neumannBoundary)*(∑ p, (T.out p:ℝ)^2*mass (T.vector p))^(2/3:ℝ)+
      ((2*Real.pi+1)/(2*b))*Real.sqrt (∑ p, (T.out p:ℝ)^2*mass (T.vector p)) := by
    have hp := mul_le_mul_of_nonneg_left hmean (show 0≤12*a*unitWindowKinetic/b^2 by exact div_nonneg (mul_nonneg (by positivity) unitWindowKinetic_nonneg) (sq_nonneg _))
    change (∑ p, mass (T.vector p))=1 at hm
    rw [hm,mul_one] at hsumgap
    change (∑ p, form S (T.vector p))≤E+B at henergy
    unfold RecordedEnsemble.deletedSquare
    linarith
  exact hGapBound
end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_AtomicGapScale
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
namespace Coulomb

lemma atomicRefinedFormula_mono {δ δ' P P' m m' a b : ℝ}
    (hd : δ ≤ δ') (hP : 0 ≤ P) (hPP : P ≤ P') (hm : 0 ≤ m) (hmm : m ≤ m')
    (ha : 0<a) (hb : 0<b) :
    atomicRefinedFormula δ P m a b ≤ atomicRefinedFormula δ' P' m' a b := by
  have hP' := hP.trans hPP
  have hm' := hm.trans hmm
  have hA := atomicPhysicalCapConstant_nonneg
  have hB := atomicPatchCountFactor_nonneg
  have hT := thinReserveFactor_nonneg
  have hU := unitWindowKinetic_nonneg
  have hN := neumannBoundary_nonneg
  unfold atomicRefinedFormula
  gcongr

lemma atomicRefinedError_eq_formula (δ P a b : ℝ) :
    atomicRefinedError δ P a b=atomicRefinedFormula δ P (screenMass δ a) a b := rfl

lemma atomicRefinedError_small_bound {δ P a : ℝ} (hδ : 0 ≤ δ)
    (hP : 0 ≤ P) (hPP : P ≤ atomicCountConstant) (ha : 0<a) (ha1 : a ≤ 1)
    (hd : δ ≤ a^(-349/50:ℝ)) :
    atomicRefinedError δ P a (a^(6/5:ℝ)) ≤
      atomicRefinedFormula (a^(-349/50:ℝ)) atomicCountConstant (2*a^(-3:ℝ)) a (a^(6/5:ℝ)) := by
  have hsmall : δ*a^7 ≤ 1 := by
    calc
      δ*a^7 ≤ a^(-349/50:ℝ)*a^7 := mul_le_mul_of_nonneg_right hd (pow_nonneg ha.le _)
      _ = a^(1/50:ℝ) := by rw [←Real.rpow_natCast a 7,←Real.rpow_add ha]; norm_num
      _ ≤ 1 := Real.rpow_le_one ha.le ha1 (by norm_num)
  have hm := NeutralAtom.screenMass_small_offset ha ha1 hδ hsmall
  have hm' : screenMass δ a ≤ 2*a^(-3:ℝ) := by
    simpa only [Real.rpow_neg ha.le,Real.rpow_ofNat,div_eq_mul_inv] using hm
  rw [atomicRefinedError_eq_formula]
  exact atomicRefinedFormula_mono hd hP hPP (screenMass_pos _ _).le hm' ha (Real.rpow_pos_of_pos ha _)

lemma mul_rpow_monomials {a : ℝ} (ha : 0<a) (c d x y : ℝ) :
    (c*a^x)*(d*a^y)=(c*d)*a^(x+y) := by rw [Real.rpow_add ha]; ring

lemma sqrt_rpow_monomial {a : ℝ} (ha : 0<a) {c : ℝ} (hc : 0 ≤ c) (x : ℝ) :
    Real.sqrt (c*a^x)=Real.sqrt c*a^(x/2) := by
  rw [Real.sqrt_mul hc]
  simp only [Real.sqrt_eq_rpow]
  rw [←Real.rpow_mul ha.le]
  congr 2
  ring

lemma div_rpow_monomial {a : ℝ} (ha : 0<a) (c x y : ℝ) :
    (c*a^x)/a^y=c*a^(x-y) := by rw [Real.rpow_sub ha]; ring

lemma atomicRefinedFormula_power_expansion {a P : ℝ} (ha : 0<a) (hP : 0 ≤ P) :
    atomicRefinedFormula (a^(-349/50:ℝ)) P (2*a^(-3:ℝ)) a (a^(6/5:ℝ)) =
      a^(-349/50:ℝ)+
      (2*thinReserveFactor*Real.sqrt P)*a^(-27/5:ℝ)+
      (12*unitWindowKinetic*Real.sqrt (4*atomicPhysicalCapConstant*P))*a^(-27/5:ℝ)+
      Real.sqrt (288*atomicPhysicalCapConstant*atomicPatchCountFactor*P^2)*a^(-69/10:ℝ)+
      (((Real.pi^2/2)*neumannBoundary)*(4*atomicPatchCountFactor*P)^(2/3:ℝ))*a^(-32/5:ℝ)+
      (((2*Real.pi+1)/2)*Real.sqrt (4*atomicPatchCountFactor*P))*a^(-21/5:ℝ) := by
  have hm2 : (2*a^(-3:ℝ))^2=4*a^(-6:ℝ) := by
    rw [mul_pow,←Real.rpow_mul_natCast ha.le]
    norm_num
  have hb2 : (a^(6/5:ℝ))^2=a^(12/5:ℝ) := by
    rw [←Real.rpow_mul_natCast ha.le]
    norm_num
  have hq : atomicPhysicalCapConstant*P*(2*a^(-3:ℝ))^2/a^2=
      (4*atomicPhysicalCapConstant*P)*a^(-8:ℝ) := by
    rw [hm2]
    calc
      _ = ((4*atomicPhysicalCapConstant*P)*a^(-6:ℝ))/a^2 := by ring
      _ = _ := by rw [←Real.rpow_natCast a 2,div_rpow_monomial ha]; norm_num
  have hn : atomicPatchCountFactor*P*(2*a^(-3:ℝ))^2=
      (4*atomicPatchCountFactor*P)*a^(-6:ℝ) := by rw [hm2]; ring
  have hd : 18*atomicPatchCountFactor*(a^(6/5:ℝ)/a)*P*(2*a^(-3:ℝ))^2=
      (72*atomicPatchCountFactor*P)*a^(-29/5:ℝ) := by
    rw [hm2]
    calc
      _ = ((72*atomicPatchCountFactor*P)*(a^(6/5:ℝ)*a^(-6:ℝ)))/a^1 := by ring
      _ = _ := by rw [←Real.rpow_add ha,←Real.rpow_natCast a 1,div_rpow_monomial ha]; norm_num
  have hqd : ((4*atomicPhysicalCapConstant*P)*a^(-8:ℝ))*
      ((72*atomicPatchCountFactor*P)*a^(-29/5:ℝ))=
      (288*atomicPhysicalCapConstant*atomicPatchCountFactor*P^2)*a^(-69/5:ℝ) := by
    rw [mul_rpow_monomials ha]
    congr 1 <;> ring_nf
  have hN0 : 0 ≤ 4*atomicPatchCountFactor*P := by positivity [atomicPatchCountFactor_nonneg]
  have hQ0 : 0 ≤ 4*atomicPhysicalCapConstant*P := by positivity [atomicPhysicalCapConstant_nonneg]
  have hQD0 : 0 ≤ 288*atomicPhysicalCapConstant*atomicPatchCountFactor*P^2 := by
    positivity [atomicPhysicalCapConstant_nonneg,atomicPatchCountFactor_nonneg]
  have hn23 : ((4*atomicPatchCountFactor*P)*a^(-6:ℝ))^(2/3:ℝ)=
      (4*atomicPatchCountFactor*P)^(2/3:ℝ)*a^(-4:ℝ) := by
    rw [Real.mul_rpow hN0 (Real.rpow_nonneg ha.le _),←Real.rpow_mul ha.le]
    norm_num
  have hsi : ((a^(6/5:ℝ))⁻¹)^2=a^(-12/5:ℝ) := by
    rw [←Real.rpow_neg ha.le,←Real.rpow_mul_natCast ha.le]
    norm_num
  unfold atomicRefinedFormula
  rw [hq,hn,hd,hqd,hb2,hsi,hn23,sqrt_rpow_monomial ha hQ0,
    sqrt_rpow_monomial ha hN0,sqrt_rpow_monomial ha hQD0]
  norm_num only
  have h1 : thinReserveFactor*(Real.sqrt P*(2*a^(-3:ℝ))/a^(12/5:ℝ))=
      (2*thinReserveFactor*Real.sqrt P)*a^(-27/5:ℝ) := by
    calc
      _ = (2*thinReserveFactor*Real.sqrt P)*a^(-3:ℝ)/a^(12/5:ℝ) := by ring
      _ = _ := by rw [div_rpow_monomial ha]; norm_num
  have h2 : 12*a*unitWindowKinetic/a^(12/5:ℝ)*
      (Real.sqrt (4*atomicPhysicalCapConstant*P)*a^(-4:ℝ))=
      (12*unitWindowKinetic*Real.sqrt (4*atomicPhysicalCapConstant*P))*a^(-27/5:ℝ) := by
    calc
      _ = (12*unitWindowKinetic*Real.sqrt (4*atomicPhysicalCapConstant*P))*(a^1*a^(-4:ℝ))/a^(12/5:ℝ) := by ring
      _ = _ := by rw [←Real.rpow_natCast a 1,←Real.rpow_add ha,div_rpow_monomial ha]; norm_num
  have h4 : a^(-12/5:ℝ)*((Real.pi^2/2)*neumannBoundary)*
      ((4*atomicPatchCountFactor*P)^(2/3:ℝ)*a^(-4:ℝ))=
      (((Real.pi^2/2)*neumannBoundary)*(4*atomicPatchCountFactor*P)^(2/3:ℝ))*a^(-32/5:ℝ) := by
    calc
      _ = (((Real.pi^2/2)*neumannBoundary)*(4*atomicPatchCountFactor*P)^(2/3:ℝ))*(a^(-12/5:ℝ)*a^(-4:ℝ)) := by ring
      _ = _ := by rw [←Real.rpow_add ha]; norm_num
  have h5 : ((2*Real.pi+1)/(2*a^(6/5:ℝ)))*(Real.sqrt (4*atomicPatchCountFactor*P)*a^(-3:ℝ))=
      (((2*Real.pi+1)/2)*Real.sqrt (4*atomicPatchCountFactor*P))*a^(-21/5:ℝ) := by
    calc
      _ = ((((2*Real.pi+1)/2)*Real.sqrt (4*atomicPatchCountFactor*P))*a^(-3:ℝ))/a^(6/5:ℝ) := by ring
      _ = _ := by rw [div_rpow_monomial ha]; norm_num
  norm_num at h1 h2 h4 h5 ⊢
  rw [h1,h2,h4,h5]

lemma atomicRefinedFormula_scaled_tendsto {P : ℝ} (hP : 0 ≤ P) :
    Tendsto (fun a : ℝ => atomicRefinedFormula (a^(-349/50:ℝ)) P
      (2*a^(-3:ℝ)) a (a^(6/5:ℝ))*a^(349/50:ℝ)) (𝓝[>] 0) (𝓝 1) := by
  have ht := (((((tendsto_const_nhds (x := (1:ℝ))).add
    ((NeutralAtom.tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<79/50)).const_mul
      (2*thinReserveFactor*Real.sqrt P))).add
    ((NeutralAtom.tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<79/50)).const_mul
      (12*unitWindowKinetic*Real.sqrt (4*atomicPhysicalCapConstant*P)))).add
    ((NeutralAtom.tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<2/25)).const_mul
      (Real.sqrt (288*atomicPhysicalCapConstant*atomicPatchCountFactor*P^2)))).add
    ((NeutralAtom.tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<29/50)).const_mul
      (((Real.pi^2/2)*neumannBoundary)*(4*atomicPatchCountFactor*P)^(2/3:ℝ)))).add
    ((NeutralAtom.tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<139/50)).const_mul
      (((2*Real.pi+1)/2)*Real.sqrt (4*atomicPatchCountFactor*P)))
  simp only [mul_zero, add_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  have ha : 0<a := ha
  rw [atomicRefinedFormula_power_expansion ha hP]
  simp only [add_mul,mul_assoc,←Real.rpow_add ha]
  norm_num

lemma exists_atomic_refined_small_scale : ∃ s : ℝ, 0 < s ∧ s≤1 ∧
    ∀ a : ℝ, 0<a → a < s →
      18*a^(6/5:ℝ)≤a ∧
      atomicRefinedFormula (a^(-349/50:ℝ)) atomicCountConstant
        (2*a^(-3:ℝ)) a (a^(6/5:ℝ)) ≤ 2*a^(-349/50:ℝ) := by
  have hP : 0 ≤ atomicCountConstant := le_trans (by norm_num) atomicCountConstant_ge_two
  have he := (atomicRefinedFormula_scaled_tendsto hP).eventually (gt_mem_nhds (by norm_num : (1:ℝ)<2))
  have hs := ((NeutralAtom.tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<1/5)).const_mul 18).eventually
    (gt_mem_nhds (by norm_num : (18:ℝ)*0<1))
  have hh : ∀ᶠ a : ℝ in 𝓝[>] 0, a<1 ∧
      atomicRefinedFormula (a^(-349/50:ℝ)) atomicCountConstant
        (2*a^(-3:ℝ)) a (a^(6/5:ℝ))*a^(349/50:ℝ)<2 ∧ 18*a^(1/5:ℝ)<1 := by
    filter_upwards [he,hs, (show ∀ᶠ a : ℝ in 𝓝[>] 0, a<1 from
      (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds)] with a ha hb hc
    exact ⟨hc,ha,hb⟩
  obtain ⟨s,hs0,hprop⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp hh
  refine ⟨min s 1, lt_min hs0 (by norm_num), min_le_right _ _, ?_⟩
  intro a ha has
  have hp := hprop ⟨ha, has.trans_le (min_le_left s 1)⟩
  constructor
  · have hx : a^(6/5:ℝ)=a^(1/5:ℝ)*a := by
      rw [show (6/5:ℝ)=1/5+1 by norm_num,Real.rpow_add ha,Real.rpow_one]
    rw [hx]
    nlinarith [mul_lt_mul_of_pos_right hp.2.2 ha]
  · have hx : a^(-349/50:ℝ)*a^(349/50:ℝ)=1 := by rw [←Real.rpow_add ha]; norm_num
    apply le_of_mul_le_mul_right (a := a^(349/50:ℝ)) _ (Real.rpow_pos_of_pos ha (349/50:ℝ))
    rw [mul_assoc,hx,mul_one]
    exact hp.2.1.le

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FreshPotentialTower
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
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
namespace Coulomb

lemma potentialForm_min_tendsto {n : ℕ} (u : H1Vector n)
    (W : Configuration n → ℝ) (hW : Measurable W) (hW0 : ∀ x,0≤W x)
    (hi : ∀ s,Integrable (fun x => W x*‖u.value s x‖^2)) :
    Tendsto (fun k : ℕ => potentialForm (fun x => min (W x) (k:ℝ)) u)
      atTop (𝓝 (potentialForm W u)) := by
  apply tendsto_finsetSum
  intro s _
  apply tendsto_integral_of_dominated_convergence (fun x => W x*‖u.value s x‖^2)
  · intro k
    exact (hW.min measurable_const).aestronglyMeasurable.mul ((u.value_L2 s).aestronglyMeasurable.norm.pow 2)
  · exact hi s
  · intro k
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (mul_nonneg (le_min (hW0 x) (Nat.cast_nonneg k)) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
  · filter_upwards [] with x
    apply Tendsto.congr' _ tendsto_const_nhds
    have he : ∀ᶠ k : ℕ in atTop, W x≤(k:ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (W x))
    exact he.mono (fun k hk => by dsimp only; rw [min_eq_left hk])

namespace RecordedEnsemble
lemma Conserves.nonnegative_observable {n : ℕ} {T : RecordedEnsemble n}
    {u : H1Vector n} (hT : T.Conserves u) (W : Configuration n → ℝ)
    (hW : Measurable W) (hW0 : ∀ x,0≤W x)
    (hi : ∀ s,Integrable (fun x => W x*‖u.value s x‖^2))
    (hTi : ∀ p s,Integrable (fun x => W (reindexConfiguration (T.labels p) x)*‖(T.vector p).value s x‖^2)) :
    (∑ p,potentialForm (W ∘ reindexConfiguration (T.labels p)) (T.vector p))=potentialForm W u := by
  have hleft : Tendsto (fun k : ℕ => ∑ p,potentialForm
      ((fun x => min (W x) (k:ℝ)) ∘ reindexConfiguration (T.labels p)) (T.vector p)) atTop
      (𝓝 (∑ p,potentialForm (W ∘ reindexConfiguration (T.labels p)) (T.vector p))) := by
    apply tendsto_finsetSum
    intro p _
    exact potentialForm_min_tendsto (T.vector p) _
      (hW.comp (reindexConfiguration_measurePreserving _).measurable) (fun x => hW0 _) (hTi p)
  have he (k : ℕ) : (∑ p,potentialForm
      ((fun x => min (W x) (k:ℝ)) ∘ reindexConfiguration (T.labels p)) (T.vector p))=
      potentialForm (fun x => min (W x) (k:ℝ)) u := by
    apply hT _ (hW.min measurable_const)
    exact ⟨k,fun x => by rw [abs_of_nonneg (le_min (hW0 x) (Nat.cast_nonneg k))]; exact min_le_right _ _⟩
  simp_rw [he] at hleft
  exact tendsto_nhds_unique hleft (potentialForm_min_tendsto u W hW hW0 hi)
end RecordedEnsemble

lemma nuclearPotential_reindex_labels {M m n : ℕ} (S : Nuclei M)
    (e : Fin m ≃ Fin n) (x : Configuration m) : nuclearPotential S (reindexConfiguration e x)=nuclearPotential S x := by
  unfold nuclearPotential
  exact (Equiv.sum_comp e (fun i => attraction S (position (reindexConfiguration e x) i))).symm.trans
    (Finset.sum_congr rfl (fun i _ => by rw [position_reindex]))

theorem RecordedEnsemble.Conserves.coulomb_potential {n : ℕ} {T : RecordedEnsemble n}
    {u : H1Vector n} (hT : T.Conserves u) (y : Space) :
    (∑ p,coreCoulombPotential (T.vector p) y)=coreCoulombPotential u y := by
  have hm : Measurable (nuclearPotential (n := n) (unitNucleus y)) :=
    Finset.measurable_sum _ (fun i _ => (attraction_measurable _).comp (positionCLM i).measurable)
  have hi := hT.nonnegative_observable (nuclearPotential (unitNucleus y)) hm
    (fun x => Finset.sum_nonneg (fun i _ => attraction_nonneg _ _))
    (u.nuclear_integrable (unitNucleus y)) (fun p s => by
      change Integrable (fun x : Configuration (T.out p+T.core p) => nuclearPotential (unitNucleus y) (reindexConfiguration (T.labels p) x)*‖(T.vector p).value s x‖^2)
      simp_rw [nuclearPotential_reindex_labels]
      exact (T.vector p).nuclear_integrable (unitNucleus y) s)
  simp only [Function.comp_def,nuclearPotential_reindex_labels] at hi
  change (∑ p,nuclearEnergy (unitNucleus y) (T.vector p))=nuclearEnergy (unitNucleus y) u at hi
  simpa only [nuclearEnergy_unit_eq_coreCoulomb] using hi

theorem fresh_core_coulomb_tower {m k : ℕ} (u : H1Vector (m+k)) (y : Space) :
    sliceExpectation u (fun s x => coreCoulombPotential (u.coreSlice s x).normalized y+
      nuclearPotential (unitNucleus y) x)=coreCoulombPotential u y := by
  have hc (s : Spins m) : Integrable (fun x => mass (u.coreSlice s x)*
      coreCoulombPotential (u.coreSlice s x).normalized y) := by
    simp only [←nuclearEnergy_unit_eq_coreCoulomb]
    change Integrable (fun x => mass (u.coreSlice s x)*potentialForm (nuclearPotential (unitNucleus y))
      (u.coreSlice s x).normalized)
    simp_rw [potentialForm_normalized_weight]
    exact potentialForm_coreSlice_integrable u s _ (fun t => u.core_nuclear_integrable (unitNucleus y) (Fin.append s t))
  have ho (s : Spins m) : Integrable (fun x => mass (u.coreSlice s x)*nuclearPotential (unitNucleus y) x) :=
    slice_weight_integrable_const u _ (u.outer_nuclear_integrable (unitNucleus y)) s
  rw [sliceExpectation_add u _ _ hc ho,sliceExpectation_const u _ (u.outer_nuclear_integrable (unitNucleus y))]
  have HH := conditional_core_nuclear_identity (unitNucleus y) u
  simp only [nuclearEnergy_unit_eq_coreCoulomb] at HH
  change sliceExpectation u (fun s x => coreCoulombPotential (u.coreSlice s x).normalized y)=_ at HH
  rw [HH,←nuclearEnergy_unit_eq_coreCoulomb,nuclearEnergy_split]
  change potentialForm _ u+potentialForm _ u=potentialForm _ u+potentialForm _ u
  ring

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_ConfigurationDensity
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

theorem integrable_cons {N : ℕ} {f : Configuration (N + 1) → ℝ}
    (hf : Integrable f) :
    Integrable (fun p : Position × Configuration N => f (Fin.cons p.1 p.2)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => Position) 0
  have he := (volume_preserving_piFinSuccAbove
    (fun _ : Fin (N + 1) => Position) 0).symm e
  have hh := (he.integrable_comp_emb e.symm.measurableEmbedding).2 hf
  simpa [e, Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Fin.insertNth_zero] using hh

theorem integral_cons {N : ℕ} {f : Configuration (N + 1) → ℝ}
    (hf : Integrable f) :
    (∫ x : Position, ∫ y : Configuration N, f (Fin.cons x y)) = ∫ z, f z := by
  rw [← integral_prod _ (integrable_cons hf)]
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => Position) 0
  have he := (volume_preserving_piFinSuccAbove
    (fun _ : Fin (N + 1) => Position) 0).symm e
  have hh := he.integral_comp' f
  simpa [MeasureTheory.Measure.volume_eq_prod, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Fin.insertNth_zero] using hh

theorem piCongrLeft_perm {ι α : Type*} (p : Equiv.Perm ι) (x : ι → α) :
    Equiv.piCongrLeft (fun _ : ι => α) p.symm x = x ∘ p := by
  funext i
  simp [Equiv.piCongrLeft_apply]

theorem configurationDensity_perm {n : ℕ} {ψ : Wavefunction n}
    (hψ : IsAntisymmetric ψ) (p : Equiv.Perm (Fin n)) :
    (fun x : Configuration n => configurationDensity ψ (x ∘ p)) =ᵐ[volume]
      configurationDensity ψ := by
  have hsign : ‖(((Equiv.Perm.sign p : ℤ) : ℂ))‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hp | hp <;> simp [hp]
  have ha : ∀ᵐ x : Configuration n ∂volume, ∀ σ : Spins n,
      ψ (σ ∘ p) (x ∘ p) = (((Equiv.Perm.sign p : ℤ) : ℂ)) * ψ σ x :=
    (ae_all_iff).mpr (hψ p)
  filter_upwards [ha] with x hx
  unfold configurationDensity
  have hsum := (Equiv.piCongrLeft (fun _ : Fin n => Fin 2) p.symm).sum_comp
    (fun σ : Spins n => ‖ψ σ (x ∘ p)‖ ^ 2)
  have hh : (∑ σ : Spins n, ‖ψ (σ ∘ p) (x ∘ p)‖ ^ 2) =
      ∑ σ : Spins n, ‖ψ σ (x ∘ p)‖ ^ 2 := by
    simpa only [piCongrLeft_perm] using hsum
  rw [← hh]
  apply Finset.sum_congr rfl
  intro σ _
  rw [hx σ, norm_mul, hsign, one_mul]

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

theorem rawExpectation_perm {n : ℕ} {ψ : Wavefunction n}
    (hψ : IsAntisymmetric ψ) (p : Equiv.Perm (Fin n)) (F : Configuration n → ℝ) :
    rawExpectation ψ (fun x => F (x ∘ p)) = rawExpectation ψ F := by
  unfold rawExpectation
  calc
    (∫ x, F (x ∘ p) * configurationDensity ψ x) =
        ∫ x, F (x ∘ p) * configurationDensity ψ (x ∘ p) := by
      apply integral_congr_ae
      filter_upwards [configurationDensity_perm hψ p] with x hx
      rw [hx]
    _ = ∫ x, F x * configurationDensity ψ x := by
      have hi := (volume_measurePreserving_piCongrLeft
        (fun _ : Fin n => Position) p.symm).integral_comp'
        (fun x => F x * configurationDensity ψ x)
      simpa only [MeasurableEquiv.coe_piCongrLeft, piCongrLeft_perm] using hi

theorem integrable_siteWeight {n : ℕ} {f : Configuration n → ℝ}
    (hf : Integrable f) {S : Set Position} (hS : MeasurableSet S) (i : Fin n) :
    Integrable (fun x : Configuration n => S.indicator (fun _ => (1 : ℝ)) (x i) * f x) := by
  have hi := hf.indicator (hS.preimage (measurable_pi_apply i))
  have heq : (fun x : Configuration n => S.indicator (fun _ => (1 : ℝ)) (x i) * f x) =
      ((fun x : Configuration n => x i) ⁻¹' S).indicator f := by
    funext x
    by_cases hx : x i ∈ S <;> simp [hx]
  rw [heq]
  exact hi

theorem rawExpectation_site {N : ℕ} {ψ : Wavefunction (N + 1)}
    (hψ : IsAntisymmetric ψ) (S : Set Position) (i : Fin (N + 1)) :
    rawExpectation ψ (fun x => S.indicator (fun _ => (1 : ℝ)) (x i)) =
      rawExpectation ψ (fun x => S.indicator (fun _ => (1 : ℝ)) (x 0)) := by
  have hp := rawExpectation_perm hψ (Equiv.swap 0 i)
    (fun x => S.indicator (fun _ => (1 : ℝ)) (x 0))
  simpa only [Function.comp_apply, Equiv.swap_apply_left] using hp

theorem rawExpectation_count_factor {N : ℕ} {ψ : Wavefunction (N + 1)}
    (hanti : IsAntisymmetric ψ) (hψ : ∀ σ, MemLp (ψ σ) 2 volume)
    {S : Set Position} (hS : MeasurableSet S) :
    rawExpectation ψ (rawCount S) =
      (N + 1 : ℝ) * rawExpectation ψ (fun x => S.indicator (fun _ => (1 : ℝ)) (x 0)) := by
  have hi := integrable_siteWeight (integrable_configurationDensity hψ) hS
  calc
    rawExpectation ψ (rawCount S) = ∑ i : Fin (N + 1),
        rawExpectation ψ (fun x => S.indicator (fun _ => (1 : ℝ)) (x i)) := by
      unfold rawExpectation rawCount
      simp_rw [Finset.sum_mul]
      exact integral_finsetSum _ fun i _ => hi i
    _ = ∑ _i : Fin (N + 1),
        rawExpectation ψ (fun x => S.indicator (fun _ => (1 : ℝ)) (x 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact rawExpectation_site hanti S i
    _ = _ := by simp

theorem density_integral_eq_first_site {N : ℕ} {ψ : Wavefunction (N + 1)}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) {S : Set Position} (hS : MeasurableSet S) :
    (∫ x in S, density ψ x) =
      (N + 1 : ℝ) * rawExpectation ψ (fun x => S.indicator (fun _ => (1 : ℝ)) (x 0)) := by
  have hw (σ : Spins (N + 1)) := integrable_siteWeight
    (hψ σ).norm.integrable_sq hS (0 : Fin (N + 1))
  have hinn (σ : Spins (N + 1)) :
      Integrable (fun x : Position => ∫ y : Configuration N, ‖ψ σ (Fin.cons x y)‖ ^ 2) :=
    (integrable_cons (hψ σ).norm.integrable_sq).integral_prod_left
  unfold density rawExpectation configurationDensity
  rw [integral_const_mul, integral_finsetSum _ (fun σ _ => (hinn σ).integrableOn)]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun σ _ => hw σ), ← Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  calc
    (∫ x in S, ∫ y : Configuration N, ‖ψ σ (Fin.cons x y)‖ ^ 2) =
        ∫ x, S.indicator (fun x => ∫ y : Configuration N, ‖ψ σ (Fin.cons x y)‖ ^ 2) x :=
      (integral_indicator hS).symm
    _ = ∫ x : Position, ∫ y : Configuration N,
        S.indicator (fun _ => (1 : ℝ)) x * ‖ψ σ (Fin.cons x y)‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ S <;> simp [hx]
    _ = _ := by simpa only [Fin.cons_zero] using integral_cons (hw σ)

theorem rawExpectation_count_eq_density {N : ℕ} {ψ : Wavefunction (N + 1)}
    (hanti : IsAntisymmetric ψ) (hψ : ∀ σ, MemLp (ψ σ) 2 volume)
    {S : Set Position} (hS : MeasurableSet S) :
    rawExpectation ψ (rawCount S) = ∫ x in S, density ψ x := by
  rw [rawExpectation_count_factor hanti hψ hS, density_integral_eq_first_site hψ hS]

theorem rawCount_nonneg {n : ℕ} (S : Set Position) (x : Configuration n) :
    0 ≤ rawCount S x := by
  apply Finset.sum_nonneg
  intro i _
  by_cases hi : x i ∈ S <;> simp [hi]

theorem rawCount_le_number {n : ℕ} (S : Set Position) (x : Configuration n) :
    rawCount S x ≤ n := by
  calc
    rawCount S x ≤ ∑ _i : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : x i ∈ S <;> simp [hi]
    _ = n := by simp

theorem measurable_rawCount {n : ℕ} {S : Set Position} (hS : MeasurableSet S) :
    Measurable (rawCount (n := n) S) := by
  apply Finset.measurable_sum
  intro i _
  exact (measurable_const.indicator hS).comp (measurable_pi_apply i)

theorem rawCount_memLp {n : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hn : normSquared ψ = 1)
    {S : Set Position} (hS : MeasurableSet S) :
    MemLp (rawCount (n := n) S) 2 (rawLaw ψ) := by
  have := rawLaw_isProbability hψ hn
  apply MemLp.of_bound (measurable_rawCount hS).aestronglyMeasurable (n : ℝ)
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (rawCount_nonneg S x)] using rawCount_le_number S x

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

lemma fromH1_weak {n : ℕ} (ψ : Coulomb.H1Vector n) :
    HasWeakGradient (fromH1Wave ψ) (fromH1Gradient ψ) := by
  intro s i a φ hφ hc
  have H := weakDirectional_pullback (flattenConfiguration n)
    (flattenConfiguration_measurePreserving n) (ψ.weak_partial s (i,a))
    (flattenConfiguration_coordinateDirection i a) φ hφ hc
  simpa only [fromH1Wave,fromH1Gradient,mul_comm] using H

lemma asH1_antisymmetric {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) : Coulomb.Antisymmetric (asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1) := by
  intro p s
  have H := (flattenConfiguration_symm_measurePreserving n).quasiMeasurePreserving.ae (hd.1 p s)
  exact H

lemma fromH1_domain {n : ℕ} (ψ : Coulomb.H1Vector n) (ha : Coulomb.Antisymmetric ψ) :
    FormDomain (fromH1Wave ψ) (fromH1Gradient ψ) := by
  refine ⟨?_, fromH1_weak ψ, ?_, ?_, ?_, ?_⟩
  · intro p s
    exact (flattenConfiguration_measurePreserving n).quasiMeasurePreserving.ae (ha p s)
  · intro s
    exact (ψ.value_L2 s).comp_measurePreserving (flattenConfiguration_measurePreserving n)
  · intro s i a
    exact (ψ.partial_L2 s (i,a)).comp_measurePreserving (flattenConfiguration_measurePreserving n)
  · intro s i
    have H := (flattenConfiguration_measurePreserving n).integrable_comp_of_integrable
      (ψ.nuclear_coulomb_integrable_bound s i 0 (by norm_num : (0:ℝ)<1)).1
    change Integrable (fun x : Configuration n => ‖x i-0‖⁻¹*‖fromH1Wave ψ s x‖^2) at H
    simpa only [sub_zero] using H
  · intro s i j hij
    exact (flattenConfiguration_measurePreserving n).integrable_comp_of_integrable
      (ψ.pair_coulomb_integrable_bound s i j hij.ne (by norm_num : (0:ℝ)<1)).1

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
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_PhysicalDensityWeighted
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
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

theorem density_weight_eq_first_site {N : ℕ} (ψ : Wavefunction (N+1))
    (W : Position → ℝ)
    (hi : ∀ σ,Integrable (fun x : Configuration (N+1) => W (x 0)*‖ψ σ x‖^2)) :
    (∫ z,W z*density ψ z)=(N+1:ℝ)*rawExpectation ψ (fun x => W (x 0)) := by
  have hw (σ : Spins (N+1)) := (integrable_cons (hi σ)).integral_prod_left
  have he (σ : Spins (N+1)) :
      (fun z => W z*(∫ x : Configuration N,‖ψ σ (Fin.cons z x)‖^2))=
      fun z => ∫ x : Configuration N,W z*‖ψ σ (Fin.cons z x)‖^2 := by
    funext z
    rw [integral_const_mul]
  have hw' (σ : Spins (N+1)) : Integrable (fun z => W z*(∫ x : Configuration N,‖ψ σ (Fin.cons z x)‖^2)) := by
    rw [he]
    simpa only [Fin.cons_zero] using hw σ
  unfold density rawExpectation configurationDensity
  simp_rw [mul_left_comm (W _) (N+1:ℝ)]
  rw [integral_const_mul]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun σ _ => hw' σ),
    integral_finsetSum _ (fun σ _ => hi σ)]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  simp_rw [he σ]
  simpa only [Fin.cons_zero] using integral_cons (hi σ)

theorem density_weight_integrable {N : ℕ} (ψ : Wavefunction (N+1))
    (W : Position → ℝ)
    (hi : ∀ σ,Integrable (fun x : Configuration (N+1) => W (x 0)*‖ψ σ x‖^2)) :
    Integrable (fun z => W z*density ψ z) := by
  have hw (σ : Spins (N+1)) := (integrable_cons (hi σ)).integral_prod_left
  have hh : (fun z => W z*density ψ z)=fun z => (N+1:ℝ)*
      ∑ σ : Spins (N+1),∫ x : Configuration N,W z*‖ψ σ (Fin.cons z x)‖^2 := by
    funext z
    simp only [density,integral_const_mul,←Finset.mul_sum]
    ring
  rw [hh]
  apply Integrable.const_mul
  exact integrable_finsetSum _ (fun σ _ => by simpa only [Fin.cons_zero] using hw σ)

theorem rawExpectation_oneBody_eq_density {N : ℕ} {ψ : Wavefunction (N+1)}
    (ha : IsAntisymmetric ψ) (W : Position → ℝ)
    (hi : ∀ σ i,Integrable (fun x : Configuration (N+1) => W (x i)*‖ψ σ x‖^2)) :
    rawExpectation ψ (fun x => ∑ i : Fin (N+1),W (x i))=∫ z,W z*density ψ z := by
  have hii (i : Fin (N+1)) : Integrable (fun x => W (x i)*configurationDensity ψ x) := by
    simp only [configurationDensity,Finset.mul_sum]
    exact integrable_finsetSum _ (fun σ _ => hi σ i)
  calc
    _=∑ i : Fin (N+1),rawExpectation ψ (fun x => W (x i)) := by
      unfold rawExpectation
      simp_rw [Finset.sum_mul]
      exact integral_finsetSum _ (fun i _ => hii i)
    _=∑ _i : Fin (N+1),rawExpectation ψ (fun x => W (x 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [Function.comp_apply,Equiv.swap_apply_left] using
        rawExpectation_perm ha (Equiv.swap 0 i) (fun x => W (x 0))
    _=_ := by rw [density_weight_eq_first_site ψ W (fun σ => hi σ 0)]; simp

lemma fromH1_coulomb_weight_integrable {n : ℕ} (u : Coulomb.H1Vector n)
    (y : Position) (σ : Spins n) (i : Fin n) :
    Integrable (fun x : Configuration n => coulombKernel (y-x i)*‖fromH1Wave u σ x‖^2) := by
  have H := (flattenConfiguration_measurePreserving n).integrable_comp_of_integrable
    (u.nuclear_coulomb_integrable_bound σ i y (by norm_num : (0:ℝ)<1)).1
  change Integrable (fun x : Configuration n => Coulomb.coulombKernel (x i-y)*‖fromH1Wave u σ x‖^2) at H
  simpa only [coulombKernel,Coulomb.coulombKernel,norm_sub_rev] using H

lemma fromH1_coulomb_near_weight_integrable {n : ℕ} (u : Coulomb.H1Vector n)
    (y : Position) (R : ℝ) (σ : Spins n) (i : Fin n) :
    Integrable (fun x : Configuration n => (Metric.closedBall y R).indicator
      (fun z => coulombKernel (y-z)) (x i)*‖fromH1Wave u σ x‖^2) := by
  have H := (fromH1_coulomb_weight_integrable u y σ i).indicator
    ((measurableSet_closedBall : MeasurableSet (Metric.closedBall y R)).preimage (measurable_pi_apply i))
  apply H.congr
  exact Eventually.of_forall fun x => by
    by_cases hx : x i∈Metric.closedBall y R <;> simp [hx]

lemma rawLaw_no_fixed_particle {N : ℕ} {ψ : Wavefunction (N+1)}
    (ha : IsAntisymmetric ψ) (hψ : ∀ σ,MemLp (ψ σ) 2 volume)
    (hn : normSquared ψ=1) (y : Position) :
    ∀ᵐ x ∂rawLaw ψ,∀ i : Fin (N+1),x i≠y := by
  have := rawLaw_isProbability hψ hn
  have hi := (rawCount_memLp hψ hn (hS := measurableSet_singleton y)).integrable (by norm_num)
  have hz : (∫ x,rawCount {y} x ∂rawLaw ψ)=0 := by
    rw [integral_rawLaw hψ,rawExpectation_count_eq_density ha hψ (measurableSet_singleton y)]
    exact setIntegral_measure_zero _ (measure_singleton y)
  have he : rawCount (n := N+1) {y}=ᵐ[rawLaw ψ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall (rawCount_nonneg {y})) hi).mp hz
  filter_upwards [he] with x hx
  intro i hiy
  have hb := Finset.single_le_sum (fun j _ => show 0≤({y}:Set Position).indicator (fun _ => (1:ℝ)) (x j) from by
    by_cases hj : x j=y <;> simp [hj]) (Finset.mem_univ i)
  change ({y}:Set Position).indicator (fun _ => (1:ℝ)) (x i) ≤ rawCount {y} x at hb
  simp [hiy,hx] at hb
  norm_num at hb
end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FermionicNear
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
namespace Coulomb

lemma nearWeight_nonneg (y : Space) (R : ℝ) (z : Space) : 0≤nearWeight y R z := by
  unfold nearWeight
  exact Set.indicator_nonneg (fun z _ => coulombKernel_nonneg _) z
lemma nearWeight_measurable (y : Space) (R : ℝ) : Measurable (nearWeight y R) :=
  (coulombKernel_measurable.comp (measurable_const.sub measurable_id)).indicator measurableSet_ball
lemma nearPotential_nonneg {n : ℕ} (y : Space) (R : ℝ) (x : Configuration n) : 0≤nearPotential y R x :=
  Finset.sum_nonneg (fun index _ => nearWeight_nonneg y R (position x index))
lemma nearPotential_integrable {n : ℕ} (u : H1Vector n) (y : Space) (R : ℝ) (s : Spins n) :
    Integrable (fun x => nearPotential y R x*‖u.value s x‖^2) := by
  have hi (i : Fin n) : Integrable (fun x => nearWeight y R (position x i)*‖u.value s x‖^2) := by
    have H := (u.nuclear_coulomb_integrable_bound s i y (by norm_num : (0:ℝ)<1)).1
    have hc : Integrable (fun x => coulombKernel (y-position x i)*‖u.value s x‖^2) := by
      simpa only [coulombKernel,norm_sub_rev] using H
    have hh := hc.indicator ((measurableSet_ball : MeasurableSet (Metric.ball y R)).preimage
      (continuous_position i).measurable)
    apply hh.congr
    filter_upwards [] with x
    by_cases hx : position x i∈Metric.ball y R <;> simp [nearWeight,hx]
  simpa only [nearPotential,Finset.sum_mul] using integrable_finsetSum _ (fun i _ => hi i)

lemma nearPotential_physical {N : ℕ} (u : H1Vector (N+1)) (hu : Antisymmetric u)
    (y : Space) (R : ℝ) : potentialForm (nearPotential y R) u=
      ∫ z in Metric.ball y R,NeutralAtom.density (NeutralAtom.fromH1Wave u) z*coulombKernel (y-z) := by
  have hd := NeutralAtom.fromH1_domain u hu
  have hi (s : NeutralAtom.Spins (N+1)) (i : Fin (N+1)) :
      Integrable (fun x : NeutralAtom.Configuration (N+1) => nearWeight y R (x i)*‖NeutralAtom.fromH1Wave u s x‖^2) := by
    have H := (NeutralAtom.fromH1_coulomb_weight_integrable u y s i).indicator
      ((measurableSet_ball : MeasurableSet (Metric.ball y R)).preimage (measurable_pi_apply i))
    apply H.congr
    filter_upwards [] with x
    by_cases hx : x i∈Metric.ball y R <;> simp [nearWeight,hx,NeutralAtom.coulombKernel,coulombKernel]
  have he : potentialForm (nearPotential y R) u=
      NeutralAtom.rawExpectation (NeutralAtom.fromH1Wave u) (fun x => ∑ i,nearWeight y R (x i)) := by
    unfold NeutralAtom.rawExpectation NeutralAtom.configurationDensity potentialForm
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ (fun s _ => by
      simpa only [Finset.sum_mul] using integrable_finsetSum _ (fun i _ => hi s i))]
    apply Finset.sum_congr rfl
    intro s _
    exact ((NeutralAtom.flattenConfiguration_measurePreserving (N+1)).integral_comp'
      (fun x => nearPotential y R x*‖u.value s x‖^2)).symm
  rw [he,NeutralAtom.rawExpectation_oneBody_eq_density hd.1 _ hi,←integral_indicator measurableSet_ball]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z∈Metric.ball y R <;> simp [nearWeight,hz,mul_comm]

lemma fermionicNearConstant_nonneg : 0≤fermionicNearConstant := by unfold fermionicNearConstant; positivity

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
namespace Coulomb
lemma nearWeight_site_integrable {n : ℕ} (u : H1Vector n) (y : Space) (R : ℝ)
    (s : Spins n) (i : Fin n) :
    Integrable (fun x => nearWeight y R (position x i)*‖u.value s x‖^2) := by
  have H := (u.nuclear_coulomb_integrable_bound s i y (by norm_num : (0:ℝ)<1)).1
  have hc : Integrable (fun x => coulombKernel (y-position x i)*‖u.value s x‖^2) := by
    simpa only [coulombKernel,norm_sub_rev] using H
  have hh := hc.indicator ((measurableSet_ball : MeasurableSet (Metric.ball y R)).preimage
    (continuous_position i).measurable)
  apply hh.congr
  filter_upwards [] with x
  by_cases hx : position x i∈Metric.ball y R <;> simp [nearWeight,hx]

lemma nearPotential_outer_integrable {m k : ℕ} (u : H1Vector (m+k)) (y : Space) (R : ℝ)
    (s : Spins (m+k)) :
    Integrable (fun x => nearPotential y R ((joinConfiguration m k).symm x).1*‖u.value s x‖^2) := by
  simp only [nearPotential,position_split_left,Finset.sum_mul]
  exact integrable_finsetSum _ (fun i _ => nearWeight_site_integrable u y R s (Fin.castAdd k i))

lemma supported_core_nearPotential {m k : ℕ} (u : H1Vector (m+k)) (y : Space) {R t : ℝ}
    (hRt : R≤t) (hs : PartlySupported u (coreIndexSet m k) {z | t≤‖z-y‖}) :
    potentialForm (nearPotential y R) u=
      potentialForm (fun x => nearPotential y R ((joinConfiguration m k).symm x).1) u := by
  apply Finset.sum_congr rfl
  intro s _
  apply integral_congr_ae
  filter_upwards [hs s] with x hx
  by_cases hz : u.value s x=0
  · simp [hz]
  have hcore (i : Fin k) : nearWeight y R (position x (Fin.natAdd m i))=0 := by
    have hout : position x (Fin.natAdd m i)∉Metric.ball y R := by
      intro hi
      have hi' : ‖position x (Fin.natAdd m i)-y‖<R := by simpa only [Metric.mem_ball,dist_eq_norm] using hi
      exact hz (hx _ ⟨i,rfl⟩ (not_le.mpr (hi'.trans_le hRt)))
    exact Set.indicator_of_notMem hout _
  simp only [nearPotential,Fin.sum_univ_add,position_split_left,hcore,Finset.sum_const_zero,add_zero]

lemma nearPotential_reindex {m n : ℕ} (e : Fin m ≃ Fin n) (y : Space) (R : ℝ)
    (x : Configuration m) : nearPotential y R (reindexConfiguration e x)=nearPotential y R x := by
  unfold nearPotential
  exact (Equiv.sum_comp e (fun i => nearWeight y R (position (reindexConfiguration e x) i))).symm.trans
    (Finset.sum_congr rfl (fun i _ => by rw [position_reindex]))
lemma nearPotential_measurable {n : ℕ} (y : Space) (R : ℝ) : Measurable (nearPotential (n := n) y R) :=
  Finset.measurable_sum _ (fun i _ => (nearWeight_measurable y R).comp (continuous_position i).measurable)

lemma RecordedEnsemble.Conserves.nearPotential {n : ℕ} {T : RecordedEnsemble n}
    {u : H1Vector n} (hT : T.Conserves u) (y : Space) (R : ℝ) :
    (∑ p,potentialForm (Coulomb.nearPotential y R) (T.vector p))=potentialForm (Coulomb.nearPotential y R) u := by
  have H := hT.nonnegative_observable (Coulomb.nearPotential y R) (nearPotential_measurable y R)
    (nearPotential_nonneg y R) (nearPotential_integrable u y R)
    (fun p s => by simpa only [nearPotential_reindex] using nearPotential_integrable (T.vector p) y R s)
  simpa only [Function.comp_def,nearPotential_reindex] using H

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_AtomicSmallPatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace Coulomb

lemma screenMass_ge_inverse_cube (δ : ℝ) {a : ℝ} (ha : 0<a) :
    a^(-3:ℝ) ≤ screenMass δ a := by
  rw [Real.rpow_neg ha.le,Real.rpow_ofNat]
  unfold screenMass screenBaseMass
  linarith [le_max_left ((a^3)⁻¹) (1:ℝ), Real.sqrt_nonneg (δ*a)]

lemma source_patch_scale_condition {a P δ : ℝ} (ha : 0<a) (ha1 : a≤1) (hP : 1≤P) :
    a≤(a^(6/5:ℝ))^2*Real.sqrt P*screenMass δ a := by
  have hb : 0≤(a^(6/5:ℝ))^2 := sq_nonneg _
  have hm := screenMass_ge_inverse_cube δ ha
  have hs := Real.one_le_sqrt.mpr hP
  have he : (a^(6/5:ℝ))^2*a^(-3:ℝ)=a^(-3/5:ℝ) := by
    rw [←Real.rpow_mul_natCast ha.le,←Real.rpow_add ha]
    norm_num
  calc
    a = a^(1:ℝ) := (Real.rpow_one _).symm
    _ ≤ a^(-3/5:ℝ) := Real.rpow_le_rpow_of_exponent_ge ha ha1 (by norm_num)
    _ = (a^(6/5:ℝ))^2*1*a^(-3:ℝ) := by rw [mul_one,he]
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hs hb) hm
      (Real.rpow_nonneg ha.le _) (mul_nonneg hb (Real.sqrt_nonneg _))

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_AtomicNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

lemma atomicNearConstant_nonneg : 0≤atomicNearConstant := by
  have hT := thinReserveFactor_nonneg
  have hA := atomicPhysicalCapConstant_nonneg
  have hB := atomicPatchCountFactor_nonneg
  have hC : 0≤atomicCountConstant := by linarith [atomicCountConstant_ge_two]
  unfold atomicNearConstant atomicKineticConstant
  exact mul_nonneg fermionicNearConstant_nonneg (by positivity)

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_BallCloudDuality
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
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
namespace Coulomb

variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]

include hΩ

lemma raw_coulomb_cauchy {f g : Space → ℝ}
    (hf : MemLp f TFExponent (volume.restrict Ω))
    (hg : MemLp g TFExponent (volume.restrict Ω))
    (hfs : ∀ x∉Ω, f x=0) (hgs : ∀ x∉Ω, g x=0) :
    (coulombBilinear f g)^2 ≤ coulombBilinear f f*coulombBilinear g g := by
  have he := tfExtend_toLp hΩ hf hfs
  have he' := tfExtend_toLp hΩ hg hgs
  have hh := tfCoulomb_cauchy hΩ (hf.toLp f) (hg.toLp g)
  change (coulombBilinear (tfExtend Ω (hf.toLp f)) (tfExtend Ω (hg.toLp g)))^2≤
    coulombBilinear (tfExtend Ω (hf.toLp f)) (tfExtend Ω (hf.toLp f))*
      coulombBilinear (tfExtend Ω (hg.toLp g)) (tfExtend Ω (hg.toLp g)) at hh
  rwa [coulombBilinear_congr_ae he he',coulombBilinear_congr_ae he he,
    coulombBilinear_congr_ae he' he'] at hh

lemma raw_coulomb_ballCloud_duality {f : Space → ℝ}
    (hf : MemLp f TFExponent (volume.restrict Ω)) (hfs : ∀ x∉Ω, f x=0)
    (y : Space) {a : ℝ} (ha : 0<a) (hb : Metric.ball y a⊆Ω) :
    (coulombBilinear f (ballCloud y a 1))^2≤(5/(2*a))*coulombBilinear f f := by
  have hg : MemLp (ballCloud y a 1) TFExponent (volume.restrict Ω) :=
    MemLp.of_bound (ballCloud_measurable a 1 y).aestronglyMeasurable
      (1/(4*Real.pi/3*a^3)) (Eventually.of_forall (fun z => by
        change ‖uniformBall a 1 (z-y)‖≤_
        rw [Real.norm_of_nonneg (uniformBall_nonneg ha zero_le_one (z-y))]
        exact uniformBall_le ha zero_le_one _))
  have hgs : ∀ x∉Ω, ballCloud y a 1 x=0 := by
    intro x hx
    change (Metric.ball (0:Space) a).indicator (fun _ => 1/(4*Real.pi/3*a^3)) (x-y)=0
    apply indicator_of_notMem
    intro hh
    apply hx
    apply hb
    simpa only [Metric.mem_ball,dist_zero_right,dist_eq_norm,sub_zero] using hh
  have H := raw_coulomb_cauchy hΩ hf hg hfs hgs
  have hq := raw_coulomb_nonneg hΩ hf hfs
  have HG := mul_le_mul_of_nonneg_left (ballCloud_coulombBilinear_bound ha zero_le_one y) hq
  apply H.trans
  convert HG using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TFNegativeGap
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical BigOperators Topology
noncomputable section
namespace Coulomb

lemma rawTFNegativeError_congr_ae (Φ : Space → ℝ) {ρ σ ρ' σ' : Space → ℝ}
    (hρ : ρ =ᵐ[volume] ρ') (hσ : σ =ᵐ[volume] σ') :
    rawTFNegativeError Φ ρ σ=rawTFNegativeError Φ ρ' σ' := by
  have hp (x : Space) : (∫ z, coulombKernel (x-z)*ρ z)=∫ z, coulombKernel (x-z)*ρ' z :=
    integral_congr_ae (hρ.mono fun z hz => by simp only [hz])
  unfold rawTFNegativeError
  apply integral_congr_ae
  filter_upwards [hσ] with x hx
  rw [hp,hx]

lemma rawTFNegativeError_tfDensity {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W =ᵐ[volume.restrict Ω] Φ)
    {f g : TFLp (volume.restrict Ω)} (hf : TFNonneg f) (hg : TFNonneg g) :
    rawTFNegativeError Φ (tfDensity Ω f) (tfDensity Ω g)=
      ∫ x in Ω, max (tfPotential f x-W x) 0*g x := by
  rw [rawTFNegativeError_congr_ae Φ (tfDensity_ae_tfExtend hΩ hf) (tfDensity_ae_tfExtend hΩ hg)]
  unfold rawTFNegativeError
  change (∫ x, max (tfPotential f x-Φ x) 0*tfExtend Ω g x)=_
  calc
    _ = ∫ x in Ω, max (tfPotential f x-Φ x) 0*g x := by
      rw [←integral_indicator hΩ]
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x∈Ω <;> simp [tfExtend,hx]
    _ = _ := integral_congr_ae (hW.mono fun x hx => by rw [hx])

lemma raw_localTF_gap_identity {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W =ᵐ[volume.restrict Ω] Φ)
    {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    coulombBilinear (fun x => tfDensity Ω f x-localTFDensity hΩ W x)
      (fun x => tfDensity Ω f x-localTFDensity hΩ W x)/2+
      rawTFBregman (localTFDensity hΩ W) (tfDensity Ω f)+
      rawTFNegativeError Φ (localTFDensity hΩ W) (tfDensity Ω f)=
    rawThomasFermiEnergy Φ (tfDensity Ω f)-rawThomasFermiEnergy Φ (localTFDensity hΩ W) := by
  unfold localTFDensity
  rw [coulombBilinear_tfDensity_sub hΩ (localTFMinimizer_nonneg hΩ W) hf,
    rawTFBregman_tfDensity hΩ (localTFMinimizer_nonneg hΩ W) hf,
    rawTFNegativeError_tfDensity hΩ Φ W hW (localTFMinimizer_nonneg hΩ W) hf,
    rawThomasFermiEnergy_tfDensity hΩ Φ W hW hf,
    rawThomasFermiEnergy_tfDensity hΩ Φ W hW (localTFMinimizer_nonneg hΩ W)]
  exact (tfEnergy_minimizer_expansion hΩ thomasFermiKineticConstant_pos W
    (localTFMinimizer_nonneg hΩ W) (fun _ hf => localTFMinimizer_minimizes hΩ W hf)).symm

lemma raw_localTF_gap_identity_density {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W =ᵐ[volume.restrict Ω] Φ)
    {σ : Space → ℝ} (hσ : MemLp σ TFExponent (volume.restrict Ω))
    (hp : ∀ᵐ x ∂volume.restrict Ω, 0 ≤ σ x) (hs : ∀ x ∉ Ω, σ x = 0) :
    coulombBilinear (fun x => σ x-localTFDensity hΩ W x)
      (fun x => σ x-localTFDensity hΩ W x)/2+
      rawTFBregman (localTFDensity hΩ W) σ+
      rawTFNegativeError Φ (localTFDensity hΩ W) σ=
    rawThomasFermiEnergy Φ σ-rawThomasFermiEnergy Φ (localTFDensity hΩ W) := by
  have he := tfDensity_rawToTFLp hΩ hσ hp hs
  have hd : (fun x => tfDensity Ω (rawToTFLp σ hσ) x-localTFDensity hΩ W x) =ᵐ[volume]
      (fun x => σ x-localTFDensity hΩ W x) := he.sub EventuallyEq.rfl
  have H := raw_localTF_gap_identity hΩ Φ W hW (rawToTFLp_nonneg hσ hp)
  rwa [coulombBilinear_congr_ae hd hd,rawTFBregman_congr_ae EventuallyEq.rfl he,
    rawTFNegativeError_congr_ae Φ EventuallyEq.rfl he,rawThomasFermiEnergy_congr_ae Φ he] at H

lemma raw_localTF_refined_gap_density {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W =ᵐ[volume.restrict Ω] Φ)
    {σ : Space → ℝ} (hσ : MemLp σ TFExponent (volume.restrict Ω))
    (hp : ∀ᵐ x ∂volume.restrict Ω, 0 ≤ σ x) (hs : ∀ x ∉ Ω, σ x = 0) :
    coulombBilinear (fun x => σ x-localTFDensity hΩ W x)
      (fun x => σ x-localTFDensity hΩ W x)/2+
      rawTFNegativeError Φ (localTFDensity hΩ W) σ ≤
    rawThomasFermiEnergy Φ σ-rawThomasFermiEnergy Φ (localTFDensity hΩ W) := by
  rw [←raw_localTF_gap_identity_density hΩ Φ W hW hσ hp hs]
  have he := tfDensity_rawToTFLp hΩ hσ hp hs
  have hb : 0 ≤ rawTFBregman (localTFDensity hΩ W) σ := by
    rw [←rawTFBregman_congr_ae EventuallyEq.rfl he]
    unfold localTFDensity
    rw [rawTFBregman_tfDensity hΩ (localTFMinimizer_nonneg hΩ W) (rawToTFLp_nonneg hσ hp)]
    exact mul_nonneg thomasFermiKineticConstant_pos.le
      (tfBregman_nonneg (localTFMinimizer_nonneg hΩ W) (rawToTFLp_nonneg hσ hp))
  linarith
end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_NewtonSubmean
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
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

end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TFOscillation
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Classical BigOperators Topology ContDiff
namespace Coulomb

variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]

include hΩ

omit [IsFiniteMeasure (volume.restrict Ω)] in
lemma tfPotential_eq_density {f : TFLp (volume.restrict Ω)} (hf : TFNonneg f) :
    tfPotential f=NeutralAtom.potentialOf (tfDensity Ω f) := by
  funext x
  apply integral_congr_ae
  filter_upwards [tfDensity_ae_tfExtend hΩ hf] with z hz
  change coulombKernel (x-z)*tfExtend Ω f z=coulombKernel (x-z)*tfDensity Ω f z
  rw [hz]

end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_PatchNegativeCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]

lemma rawTF_negativeError_le_gap (Φ : Space → ℝ)
    (W : TFLq (volume.restrict Ω)) (hW : W =ᵐ[volume.restrict Ω] Φ)
    {σ : Space → ℝ} (hσ : MemLp σ TFExponent (volume.restrict Ω))
    (hp : ∀ᵐ x, 0 ≤ σ x) (hs : ∀ x ∉ Ω, σ x=0) :
    rawTFNegativeError Φ (localTFDensity hΩ W) σ ≤
      rawThomasFermiEnergy Φ σ-rawThomasFermiEnergy Φ (localTFDensity hΩ W) := by
  have H := raw_localTF_refined_gap_density hΩ Φ W hW hσ (ae_restrict_of_ae hp) hs
  have hρ : MemLp (localTFDensity hΩ W) TFExponent volume :=
    tfDensity_memLp hΩ (localTFMinimizer_nonneg hΩ W)
  have hpQ := raw_coulomb_nonneg hΩ (hσ.sub (hρ.restrict (s := Ω)))
    (fun x hx => by change σ x-localTFDensity hΩ W x=0; rw [hs x hx,show localTFDensity hΩ W x=0 from tfDensity_eq_zero _ hx,sub_self])
  change 0 ≤ coulombBilinear (fun x => σ x-localTFDensity hΩ W x)
    (fun x => σ x-localTFDensity hΩ W x) at hpQ
  linarith

end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma patchSliceTFGap_nonneg {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (ht : t≤6*a) (y : Space)
    (hn : ∀ j, 20*a≤‖S.position j-y‖) (s : Spins m) (x : Configuration m) :
    0≤patchSliceTFGap S u ha hb ht y hn s x := by
  have H := rawTF_negativeError_le_gap measurableSet_ball
    (coreScreenedField S (u.coreSlice s x).normalized) _
    (coreTFField_coe S _ measurableSet_ball ha (patch_nucleus_separation S ha hb ht y hn))
    (retainedFineDensity_memLp hb (patchRetained y t b x) (position x))
    (Eventually.of_forall (fun z => retainedFineDensity_nonneg b _ _ z))
    (retainedFineDensity_patch_support hb y t x)
  apply le_trans _ H
  exact integral_nonneg (fun z => mul_nonneg (le_max_right _ _)
    (retainedFineDensity_nonneg b _ _ z))

lemma patchSliceTFGap_weight_integrable {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (ht : t≤6*a) (y : Space)
    (hn : ∀ j, 20*a≤‖S.position j-y‖) (s : Spins m)
    (hcs : ∀ᵐ x, SpatiallySupported (u.coreSlice s x).normalized {z | t≤‖z-y‖}) :
    Integrable (fun x => mass (u.coreSlice s x)*patchSliceTFGap S u ha hb ht y hn s x) := by
  have hT := (coreTF_conditional_integrable measurableSet_ball S u s ha
    (patch_nucleus_separation S ha hb ht y hn) (show 0<12*a by positivity)
    (patch_diameter ha hb ht y) (fun _ => totalCharge S/a)
    (Eventually.of_forall (fun _ => div_nonneg (totalCharge_nonneg S) ha.le))
    ((mass_coreSlice_integrable u s).mul_const ((totalCharge S/a)^2))
    (show ∀ᵐ x, ∀ z∈Metric.ball y (t-4*b),
      coreScreenedField S (u.coreSlice s x).normalized z≤totalCharge S/a from ?_)).2
  · have hF : Integrable (fun x => mass (u.coreSlice s x)*
        rawThomasFermiEnergy (coreScreenedField S (u.coreSlice s x).normalized)
          (retainedFineDensity b (patchRetained y t b x) (position x))) := by
      apply (discreteFineTF_weight_integrable S u hb (patchRetained y t b)
        (patchRetained_measurable y t b) s).congr
      filter_upwards [hcs] with x hx
      rw [discreteFineTF_eq_raw S u hb (patchRetained y t b) s x hx ?_
        (patch_retained_separated ha hb y x)]
      intro j i hi
      have hret := (patchRetained_mem ..).mp hi
      have H := norm_sub_le_norm_sub_add_norm_sub (S.position j) (position x i) y
      have hs : Real.sqrt 3≤2 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by norm_num⟩
      nlinarith [hn j]
    apply (hF.sub hT).congr
    filter_upwards [] with x
    simp only [patchSliceTFGap,Pi.sub_apply,mul_sub]
  · filter_upwards [] with x
    intro z hz
    apply (sub_le_self _ (coreCoulombPotential_nonneg _ z)).trans
    exact attraction_le_totalCharge_div S ha z
      (fun j => patch_nucleus_separation S ha hb ht y hn j z hz)

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_CoulombTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma ballCloud_norm_bound {a : ℝ} (ha : 0<a) (y z : Space) :
    ‖ballCloud y a 1 z‖≤1/(4*Real.pi/3*a^3) := by
  change ‖uniformBall a 1 (z-y)‖≤_
  rw [Real.norm_of_nonneg (uniformBall_nonneg ha zero_le_one _)]
  exact uniformBall_le ha zero_le_one _

lemma density_ballCloud_test_integrable {ρ : Space → ℝ} (hi : Integrable ρ)
    (hm : Measurable ρ) {a : ℝ} (ha : 0<a) (y : Space) :
    Integrable (fun x => ρ x*(∫ z, coulombKernel (x-z)*ballCloud y a 1 z)) := by
  have H := (coulomb_pair_integrable hi hm (ballCloud_integrable a 1 y)
    (ballCloud_measurable a 1 y) (ballCloud_norm_bound ha y)).integral_prod_left
  apply H.congr
  filter_upwards [] with x
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  ring

lemma potential_ballCloud_remainder {ρ : Space → ℝ} (hi : Integrable ρ)
    (hm : Measurable ρ) (hp : ∀ x, 0≤ρ x) {a : ℝ} (ha : 0<a) (y : Space)
    (hK : Integrable (fun x => coulombKernel (y-x)*ρ x)) :
    0≤NeutralAtom.potentialOf ρ y-coulombBilinear ρ (ballCloud y a 1) ∧
    NeutralAtom.potentialOf ρ y-coulombBilinear ρ (ballCloud y a 1)≤
      ∫ x in Metric.ball y a, ρ x*coulombKernel (y-x) := by
  have ht := density_ballCloud_test_integrable hi hm ha y
  let f := fun x => coulombKernel (y-x)*ρ x-
    ρ x*(∫ z, coulombKernel (x-z)*ballCloud y a 1 z)
  have he : NeutralAtom.potentialOf ρ y-coulombBilinear ρ (ballCloud y a 1)=∫ x, f x := by
    rw [coulombBilinear_iterated hi hm (ballCloud_integrable a 1 y)
      (ballCloud_measurable a 1 y) (ballCloud_norm_bound ha y)]
    exact (integral_sub hK ht).symm
  have hbound : ∀ᵐ x, 0≤f x ∧ f x≤(Metric.ball y a).indicator
      (fun x => ρ x*coulombKernel (y-x)) x := by
    filter_upwards [volume.ae_ne y] with x hxy
    have hlu := ballCloud_coulomb_le ha zero_le_one y x hxy
    have hl : 0≤∫ z, coulombKernel (x-z)*ballCloud y a 1 z :=
      integral_nonneg (fun z => mul_nonneg (coulombKernel_nonneg _) (uniformBall_nonneg ha zero_le_one _))
    have hpos : 0≤f x := by
      dsimp only [f]
      simp only [one_mul,coulombKernel_sub_comm x y] at hlu
      nlinarith [mul_le_mul_of_nonneg_left hlu (hp x)]
    refine ⟨hpos,?_⟩
    by_cases hx : x∈Metric.ball y a
    · rw [indicator_of_mem hx]
      dsimp only [f]
      nlinarith [mul_nonneg (hp x) hl]
    · rw [indicator_of_notMem hx]
      have hx' : a≤‖x-y‖ := by simpa only [Metric.mem_ball,dist_eq_norm,not_lt] using hx
      dsimp only [f]
      rw [ballCloud_coulomb ha zero_le_one y x hx',one_mul,coulombKernel_sub_comm x y]
      nlinarith
  rw [he]
  refine ⟨integral_nonneg_of_ae (hbound.mono (fun _ h => h.1)),?_⟩
  rw [←integral_indicator measurableSet_ball]
  apply integral_mono_ae (hK.sub ht)
  · exact (hK.congr (Eventually.of_forall (fun x => mul_comm _ _))).indicator measurableSet_ball
  · exact hbound.mono (fun _ h => h.2)

lemma coulombBilinear_sub_ballCloud {ρ σ : Space → ℝ}
    (hρ : Integrable ρ) (hρm : Measurable ρ) (hσ : Integrable σ) (hσm : Measurable σ)
    {a : ℝ} (ha : 0<a) (y : Space) :
    coulombBilinear (fun z => ρ z-σ z) (ballCloud y a 1)=
      coulombBilinear ρ (ballCloud y a 1)-coulombBilinear σ (ballCloud y a 1) := by
  change coulombBilinear (ρ-σ) (ballCloud y a 1)=_
  rw [coulombBilinear_iterated (hρ.sub hσ) (hρm.sub hσm)
    (ballCloud_integrable a 1 y) (ballCloud_measurable a 1 y) (ballCloud_norm_bound ha y),
    coulombBilinear_iterated hρ hρm (ballCloud_integrable a 1 y)
      (ballCloud_measurable a 1 y) (ballCloud_norm_bound ha y),
    coulombBilinear_iterated hσ hσm (ballCloud_integrable a 1 y)
      (ballCloud_measurable a 1 y) (ballCloud_norm_bound ha y)]
  simp only [Pi.sub_apply, sub_mul]
  exact integral_sub (density_ballCloud_test_integrable hρ hρm ha y)
    (density_ballCloud_test_integrable hσ hσm ha y)

theorem potential_difference_coulomb_transfer {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] {ρ σ : Space → ℝ}
    (hρ : MemLp ρ TFExponent (volume.restrict Ω))
    (hσ : MemLp σ TFExponent (volume.restrict Ω))
    (hρm : Measurable ρ) (hσm : Measurable σ)
    (hρp : ∀ z, 0≤ρ z) (hσp : ∀ z, 0≤σ z)
    (hρs : ∀ z∉Ω, ρ z=0) (hσs : ∀ z∉Ω, σ z=0)
    {a : ℝ} (ha : 0<a) (y : Space) (hball : Metric.ball y a⊆Ω) :
    |NeutralAtom.potentialOf ρ y-NeutralAtom.potentialOf σ y|≤
      Real.sqrt ((5/(2*a))*coulombBilinear (fun z => ρ z-σ z) (fun z => ρ z-σ z))+
      (∫ z in Metric.ball y a, ρ z*coulombKernel (y-z))+
      (∫ z in Metric.ball y a, σ z*coulombKernel (y-z)) := by
  have hρe := tfExtend_toLp hΩ hρ hρs
  have hσe := tfExtend_toLp hΩ hσ hσs
  have hρi : Integrable ρ := (tfExtend_integrable hΩ (hρ.toLp ρ)).congr hρe
  have hσi : Integrable σ := (tfExtend_integrable hΩ (hσ.toLp σ)).congr hσe
  have hρl : MemLp ρ TFExponent volume := (memLp_congr_ae hρe).mp (tfExtend_memLp hΩ _)
  have hσl : MemLp σ TFExponent volume := (memLp_congr_ae hσe).mp (tfExtend_memLp hΩ _)
  have hρpow := integrable_rpow_of_memLp_nonneg (by norm_num : (0:ℝ)<5/3) hρl
    (Eventually.of_forall hρp)
  have hσpow := integrable_rpow_of_memLp_nonneg (by norm_num : (0:ℝ)<5/3) hσl
    (Eventually.of_forall hσp)
  have Hρ := potential_ballCloud_remainder hρi hρm hρp ha y
    (density_coulomb_integrable _ hρp hρm hρi hρpow y)
  have Hσ := potential_ballCloud_remainder hσi hσm hσp ha y
    (density_coulomb_integrable _ hσp hσm hσi hσpow y)
  have hs : ∀ z∉Ω, ρ z-σ z=0 := fun z hz => by rw [hρs z hz,hσs z hz,sub_self]
  have H := raw_coulomb_ballCloud_duality hΩ (hρ.sub hσ) hs y ha hball
  have hq : 0≤(5/(2*a))*coulombBilinear (fun z => ρ z-σ z) (fun z => ρ z-σ z) :=
    mul_nonneg (by positivity) (raw_coulomb_nonneg hΩ (hρ.sub hσ) hs)
  have HT : |coulombBilinear (fun z => ρ z-σ z) (ballCloud y a 1)|≤Real.sqrt
      ((5/(2*a))*coulombBilinear (fun z => ρ z-σ z) (fun z => ρ z-σ z)) := by
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs,Real.sq_sqrt hq]
    exact H
  rw [coulombBilinear_sub_ballCloud hρi hρm hσi hσm ha y] at HT
  have HH := abs_le.mp HT
  apply abs_le.mpr
  constructor <;> linarith [Hρ.1,Hρ.2,Hσ.1,Hσ.2]

end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma translated_coulomb_ball_integral (y : Space) {r : ℝ} (hr : 0 ≤ r) :
    (∫ z in Metric.ball y r, coulombKernel (y-z))=2*Real.pi*r^2 := by
  have he : (Metric.ball y r).indicator (fun z => coulombKernel (y-z))=
      fun z => (Metric.ball (0:Space) r).indicator coulombKernel (y-z) := by
    funext z
    have hh : y-z∈Metric.ball (0:Space) r ↔ z∈Metric.ball y r := by
      simp only [Metric.mem_ball,dist_eq_norm,sub_zero,norm_sub_rev]
    by_cases hz : z∈Metric.ball y r <;> simp [hh,hz]
  rw [←integral_indicator measurableSet_ball,he,integral_sub_left_eq_self,
    integral_indicator measurableSet_ball,coulombKernel_ball_integral hr]

lemma translated_coulomb_integrableOn_ball (y : Space) (r : ℝ) :
    IntegrableOn (fun z => coulombKernel (y-z)) (Metric.ball y r) := by
  rw [←integrable_indicator_iff measurableSet_ball]
  have he : (Metric.ball y r).indicator (fun z => coulombKernel (y-z))=
      fun z => (Metric.ball (0:Space) r).indicator coulombKernel (y-z) := by
    funext z
    have hh : y-z∈Metric.ball (0:Space) r ↔ z∈Metric.ball y r := by
      simp only [Metric.mem_ball,dist_eq_norm,sub_zero,norm_sub_rev]
    by_cases hz : z∈Metric.ball y r <;> simp [hh,hz]
  rw [he]
  exact (integrable_comp_sub_left _ y).mpr
    ((coulombKernel_integrableOn_ball r).integrable_indicator measurableSet_ball)

lemma near_coulomb_of_density_cap {ρ : Space → ℝ} (y : Space) {r B : ℝ} (hr : 0 ≤ r)
    (hi : IntegrableOn (fun z => ρ z*coulombKernel (y-z)) (Metric.ball y r))
    (hc : ∀ᵐ z ∂volume.restrict (Metric.ball y r), ρ z≤B) :
    (∫ z in Metric.ball y r, ρ z*coulombKernel (y-z))≤B*(2*Real.pi*r^2) := by
  calc
    _≤∫ z in Metric.ball y r, B*coulombKernel (y-z) := by
      apply integral_mono_ae hi ((translated_coulomb_integrableOn_ball y r).const_mul B)
      exact hc.mono (fun z hz => mul_le_mul_of_nonneg_right hz (coulombKernel_nonneg _))
    _=_ := by rw [integral_const_mul,translated_coulomb_ball_integral y hr]

theorem patch_tf_density_cap {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
    (hu : SpatiallySupported u {z | t≤‖z-y‖})
    (hn : ∀ j, 20*a≤‖S.position j-y‖) :
    ∀ᵐ z ∂volume.restrict (Metric.closedBall y (3*a)),
      localTFDensity measurableSet_ball (coreTFField S u measurableSet_ball ha
        (patch_nucleus_separation S ha hb ht.2 y hn)) z≤
        (tfInteriorConstant thomasFermiKineticConstant/
          (thomasFermiKineticConstant*(5/3:ℝ)))^(3/2:ℝ)/a^6 := by
  let W := coreTFField S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn)
  have hW : ∀ᵐ z ∂volume.restrict (Metric.ball y (t-4*b)), W z≤totalCharge S/a := by
    filter_upwards [coreTFField_coe S u measurableSet_ball ha
      (patch_nucleus_separation S ha hb ht.2 y hn),ae_restrict_mem measurableSet_ball] with z hz hmem
    rw [hz]
    exact (sub_le_self _ (coreCoulombPotential_nonneg u z)).trans
      (attraction_le_totalCharge_div S ha z
        (fun j => patch_nucleus_separation S ha hb ht.2 y hn j z hmem))
  exact tfDensity_interior_bound measurableSet_ball thomasFermiKineticConstant_pos
    (div_nonneg (totalCharge_nonneg S) ha.le) W hW
    (localTFMinimizer_nonneg measurableSet_ball W)
    (fun g hg => localTFMinimizer_minimizes measurableSet_ball W hg)
    (patch_continuous_field S u ha hb ht.2 y hu hn) Metric.isOpen_ball
    (coreTFField_coe S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn))
    (patch_harmonic_field S u ha hb ht.2 y hu hn) ha (patch_inner_ball ha hb hsmall ht.1 y)

theorem patch_potential_transfer {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t r : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
    (hn : ∀ j, 20*a≤‖S.position j-y‖) (hr : 0 < r) (hra : r≤a)
    (spin : Spins m) (x : Configuration m)
    (hcs : SpatiallySupported (u.coreSlice spin x).normalized {z | t≤‖z-y‖}) :
    let W := coreTFField S (u.coreSlice spin x).normalized measurableSet_ball ha
      (patch_nucleus_separation S ha hb ht.2 y hn)
    let σ := retainedFineDensity b (patchRetained y t b x) (position x)
    |NeutralAtom.potentialOf σ y-tfPotential (localTFMinimizer measurableSet_ball W) y|≤
      Real.sqrt ((5/r)*patchSliceTFGap S u ha hb ht.2 y hn spin x)+
      (∫ z in Metric.ball y r, σ z*coulombKernel (y-z))+
      ((tfInteriorConstant thomasFermiKineticConstant/
          (thomasFermiKineticConstant*(5/3:ℝ)))^(3/2:ℝ)/a^6)*(2*Real.pi*r^2) := by
  intro W σ
  let Ω := Metric.ball y (t-4*b)
  let ρ := localTFDensity measurableSet_ball W
  have hσ : MemLp σ TFExponent (volume.restrict Ω) := retainedFineDensity_memLp hb _ _
  have hρ : MemLp ρ TFExponent volume := tfDensity_memLp measurableSet_ball
    (localTFMinimizer_nonneg measurableSet_ball W)
  have hσs : ∀ z∉Ω, σ z=0 := retainedFineDensity_patch_support hb y t x
  have hρs : ∀ z∉Ω, ρ z=0 := fun z hz => tfDensity_eq_zero _ hz
  have hball : Metric.ball y r⊆Ω := by
    apply Metric.ball_subset_ball
    linarith [ht.1]
  have H := potential_difference_coulomb_transfer measurableSet_ball hσ (hρ.restrict (s := Ω))
    (retainedFineDensity_measurable b _ _) (tfDensity_measurable measurableSet_ball _)
    (retainedFineDensity_nonneg b _ _) (tfDensity_nonneg _) hσs hρs hr y hball
  have HG := rawTF_gap_coulomb measurableSet_ball
    (coreScreenedField S (u.coreSlice spin x).normalized) W
    (coreTFField_coe S _ measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn)) hσ
    (Eventually.of_forall (retainedFineDensity_nonneg b _ _)) hσs
  have Hsq : Real.sqrt ((5/(2*r))*coulombBilinear (fun z => σ z-ρ z) (fun z => σ z-ρ z))≤
      Real.sqrt ((5/r)*patchSliceTFGap S u ha hb ht.2 y hn spin x) := by
    apply Real.sqrt_le_sqrt
    have HH := mul_le_mul_of_nonneg_left HG (show 0≤5/(2*r) by positivity)
    convert HH using 1 <;> (try dsimp only [patchSliceTFGap,σ,ρ,W]) <;> first | rfl | ring
  have hiρ : Integrable ρ := (tfExtend_integrable measurableSet_ball
    (localTFMinimizer measurableSet_ball W)).congr
      (tfDensity_ae_tfExtend measurableSet_ball (localTFMinimizer_nonneg measurableSet_ball W)).symm
  have hnear := near_coulomb_of_density_cap y hr.le
    (((density_coulomb_integrable ρ (tfDensity_nonneg _) (tfDensity_measurable measurableSet_ball _)
      hiρ (tfDensity_power_integrable measurableSet_ball (localTFMinimizer_nonneg measurableSet_ball W)) y).congr
        (Eventually.of_forall (fun z => mul_comm _ _))).integrableOn (s := Metric.ball y r))
    (ae_restrict_of_ae_restrict_of_subset
      (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith : r≤3*a)))
      (patch_tf_density_cap S (u.coreSlice spin x).normalized ha hb hsmall ht y hcs hn))
  rw [tfPotential_eq_density measurableSet_ball (localTFMinimizer_nonneg measurableSet_ball W)]
  exact H.trans (add_le_add (add_le_add Hsq le_rfl) hnear)

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_FineNear
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
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
namespace Coulomb

lemma fineKernel_near_coulomb_le {b : ℝ} (hb : 0<b) (y w : Space)
    (hw : w≠y) (r : ℝ) :
    (∫ z in Metric.ball y r,coulombKernel (y-z)*fineKernel b (z-w))≤nearWeight y (r+2*b) w := by
  by_cases hn : w∈Metric.ball y (r+2*b)
  · rw [nearWeight,indicator_of_mem hn]
    calc
      _≤∫ z,coulombKernel (y-z)*fineKernel b (z-w) :=
        setIntegral_le_integral (fineKernel_shift_coulomb_integrable hb y w)
          (Eventually.of_forall (fun z => mul_nonneg (coulombKernel_nonneg _) (fineKernel_nonneg ..)))
      _≤_ := by
        rw [fineKernel_shift_coulomb_integral]
        exact fineKernel_coulomb_le hb (sub_ne_zero.mpr hw.symm)
  · rw [nearWeight,indicator_of_notMem hn]
    have hdist : r+2*b≤‖w-y‖ := by simpa only [Metric.mem_ball,dist_eq_norm,not_lt] using hn
    have he : (∫ z in Metric.ball y r,coulombKernel (y-z)*fineKernel b (z-w))=0 := by
      apply setIntegral_eq_zero_of_ae_eq_zero
      exact Eventually.of_forall (fun z hz => by
      have hz' : ‖z-y‖ < r := by simpa only [Metric.mem_ball,dist_eq_norm] using hz
      have htri := norm_sub_le_norm_sub_add_norm_sub w z y
      rw [norm_sub_rev w z] at htri
      rw [fineKernel_eq_zero_of_two_mul_lt hb _ (by linarith),mul_zero])
    exact he.le

theorem retainedFine_near_le {n : ℕ} {b : ℝ} (hb : 0<b) (y : Space) (r : ℝ)
    (I : Finset (Fin n)) (x : Configuration n) (hxy : ∀ i,position x i≠y) :
    (∫ z in Metric.ball y r,coulombKernel (y-z)*retainedFineDensity b I (position x) z)≤
      nearPotential y (r+2*b) x := by
  simp only [retainedFineDensity,Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => (fineKernel_shift_coulomb_integrable hb y (position x i)).integrableOn)]
  exact (Finset.sum_le_sum (fun i _ => fineKernel_near_coulomb_le hb y (position x i) (hxy i) r)).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I) (fun i _ _ => nearWeight_nonneg y _ _))

lemma fineKernel_raw_deficit {b : ℝ} (hb : 0<b) (y w : Space) (hw : w≠y) :
    0 ≤ coulombKernel (y-w)-(∫ z,coulombKernel (y-z)*fineKernel b (z-w)) ∧
    coulombKernel (y-w)-(∫ z,coulombKernel (y-z)*fineKernel b (z-w))≤nearWeight y (2*b) w := by
  have hnewton : (∫ z,coulombKernel (y-z)*fineKernel b (z-w)) ≤ coulombKernel (y-w) := by
    rw [fineKernel_shift_coulomb_integral]
    exact fineKernel_coulomb_le hb (sub_ne_zero.mpr hw.symm)
  refine ⟨sub_nonneg.mpr hnewton,?_⟩
  by_cases hn : w∈Metric.ball y (2*b)
  · rw [nearWeight,indicator_of_mem hn]
    exact sub_le_self _ (integral_nonneg (fun z => mul_nonneg (coulombKernel_nonneg _) (fineKernel_nonneg ..)))
  · rw [nearWeight,indicator_of_notMem hn]
    have hsep : Real.sqrt 3*b≤‖y-w‖ := by
      have hd : 2*b≤‖w-y‖ := by simpa only [Metric.mem_ball,dist_eq_norm,not_lt] using hn
      have hs : Real.sqrt 3≤2 := by apply (Real.sqrt_le_iff).mpr; norm_num
      rw [norm_sub_rev]
      exact (mul_le_mul_of_nonneg_right hs hb.le).trans hd
    rw [fineKernel_shift_coulomb_eq hb y w hsep,sub_self]

theorem patchFine_raw_deficit {n : ℕ} {b t a : ℝ} (hb : 0<b) (ha : 0<a)
    (hat : a≤t-7*b) (y : Space) (x : Configuration n) (hxy : ∀ i,position x i≠y) :
    0≤nuclearPotential (unitNucleus y) x-
      NeutralAtom.potentialOf (retainedFineDensity b (patchRetained y t b x) (position x)) y ∧
    nuclearPotential (unitNucleus y) x-
      NeutralAtom.potentialOf (retainedFineDensity b (patchRetained y t b x) (position x)) y≤
      nearPotential y (2*b) x+((deletedLabels (patchRetained y t b) x).card:ℝ)/a := by
  let I := patchRetained y t b x
  let D := deletedLabels (patchRetained y t b) x
  have hpot : NeutralAtom.potentialOf (retainedFineDensity b I (position x)) y=
      ∑ i∈I,∫ z,coulombKernel (y-z)*fineKernel b (z-position x i) := by
    unfold NeutralAtom.potentialOf
    simp only [retainedFineDensity,Finset.mul_sum]
    exact integral_finsetSum _ (fun i _ => fineKernel_shift_coulomb_integrable hb y _)
  have hraw : nuclearPotential (unitNucleus y) x=∑ i,coulombKernel (y-position x i) := by
    simp [nuclearPotential,attraction,unitNucleus,coulombKernel,norm_sub_rev]
  have hdel : (∑ i∈D,coulombKernel (y-position x i))≤(D.card:ℝ)/a := by
    calc
      _≤∑ _i∈D,a⁻¹ := by
        apply Finset.sum_le_sum
        intro i hi
        have hni : i∉I := by simpa only [D,deletedLabels,Finset.mem_sdiff,Finset.mem_univ,true_and] using hi
        have hn : t-7*b≤‖position x i-y‖ := by simpa only [I,patchRetained_mem,not_lt] using hni
        unfold coulombKernel
        rw [norm_sub_rev]
        exact inv_anti₀ ha (hat.trans hn)
      _=_ := by simp [div_eq_mul_inv]
  have he : nuclearPotential (unitNucleus y) x-NeutralAtom.potentialOf (retainedFineDensity b I (position x)) y=
      (∑ i∈I,(coulombKernel (y-position x i)-(∫ z,coulombKernel (y-z)*fineKernel b (z-position x i))))+
        ∑ i∈D,coulombKernel (y-position x i) := by
    rw [hraw,hpot,←retained_deleted_sum (patchRetained y t b) x (fun i => coulombKernel (y-position x i)),Finset.sum_sub_distrib]
    ring
  change 0≤nuclearPotential (unitNucleus y) x-NeutralAtom.potentialOf (retainedFineDensity b I (position x)) y ∧ _
  rw [he]
  constructor
  · exact add_nonneg (Finset.sum_nonneg (fun i _ => (fineKernel_raw_deficit hb y _ (hxy i)).1))
      (Finset.sum_nonneg (fun i _ => coulombKernel_nonneg _))
  · have hh := (Finset.sum_le_sum (fun i (_ : i∈I) => (fineKernel_raw_deficit hb y _ (hxy i)).2)).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I) (fun i _ _ => nearWeight_nonneg y (2*b) _))
    exact add_le_add hh hdel
end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_PatchRawTransfer
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
namespace Coulomb

lemma sqrt_young (x : ℝ) (hx : 0≤x) {ε : ℝ} (hε : 0<ε) :
    Real.sqrt x≤ε+x/(4*ε) := by
  have h := sq_nonneg (Real.sqrt x-2*ε)
  rw [sub_sq,Real.sq_sqrt hx] at h
  have he : x/(4*ε)*(4*ε)=x := div_mul_cancel₀ _ (by positivity)
  apply (mul_le_mul_iff_of_pos_right (show 0<4*ε by positivity)).mp
  nlinarith

theorem patch_raw_field_transfer {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t r : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
    (hn : ∀ j, 20*a≤‖S.position j-y‖) (hr : 0 < r) (hra : r≤a)
    (spin : Spins m) (x : Configuration m)
    (hcs : SpatiallySupported (u.coreSlice spin x).normalized {z | t≤‖z-y‖})
    (hxy : ∀ i,position x i≠y) :
    |(coreScreenedField S (u.coreSlice spin x).normalized y-nuclearPotential (unitNucleus y) x)-
      patchTFScreenedField S (u.coreSlice spin x).normalized ha hb ht.2 y hn y|≤
      Real.sqrt ((5/r)*patchSliceTFGap S u ha hb ht.2 y hn spin x)+
      nearPotential y (r+2*b) x+nearPotential y (2*b) x+
      ((deletedLabels (patchRetained y t b) x).card:ℝ)/a+
      ((tfInteriorConstant thomasFermiKineticConstant/
        (thomasFermiKineticConstant*(5/3:ℝ)))^(3/2:ℝ)/a^6)*(2*Real.pi*r^2) := by
  let σ := retainedFineDensity b (patchRetained y t b x) (position x)
  let W := coreTFField S (u.coreSlice spin x).normalized measurableSet_ball ha
    (patch_nucleus_separation S ha hb ht.2 y hn)
  have hf := patch_potential_transfer S u ha hb hsmall ht y hn hr hra spin x hcs
  have hn' := retainedFine_near_le hb y r (patchRetained y t b x) x hxy
  have hdiff := patchFine_raw_deficit (t := t) hb ha (by linarith [ht.1]) y x hxy
  have ht' := abs_sub_le (nuclearPotential (unitNucleus y) x) (NeutralAtom.potentialOf σ y)
    (tfPotential (localTFMinimizer measurableSet_ball W) y)
  rw [abs_of_nonneg hdiff.1] at ht'
  have he : |(coreScreenedField S (u.coreSlice spin x).normalized y-nuclearPotential (unitNucleus y) x)-
      patchTFScreenedField S (u.coreSlice spin x).normalized ha hb ht.2 y hn y|=
      |nuclearPotential (unitNucleus y) x-tfPotential (localTFMinimizer measurableSet_ball W) y| := by
    unfold patchTFScreenedField
    rw [show (coreScreenedField S (u.coreSlice spin x).normalized y-nuclearPotential (unitNucleus y) x)-
        (coreScreenedField S (u.coreSlice spin x).normalized y-tfPotential
        (localTFMinimizer measurableSet_ball W) y)=
        -(nuclearPotential (unitNucleus y) x-tfPotential (localTFMinimizer measurableSet_ball W) y) by ring,
      abs_neg]
  rw [he]
  have heint : (∫ z in Metric.ball y r,σ z*coulombKernel (y-z))=
      (∫ z in Metric.ball y r,coulombKernel (y-z)*σ z) := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => mul_comm _ _)
  dsimp only [σ,W] at ht' heint
  dsimp only at hf
  rw [heint] at hf
  linarith
end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TFPotentialParameter
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
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
namespace Coulomb
variable {Ω : Set Space} (hΩ : MeasurableSet Ω)
include hΩ

variable [IsFiniteMeasure (volume.restrict Ω)]

lemma continuous_tfPotential_evaluation (y : Space) :
    Continuous (fun f : TFLp (volume.restrict Ω) => tfPotential f y) :=
  (tfPotentialEvaluation hΩ y).continuous

lemma aestronglyMeasurable_localTFPotential {A : Type*} [MeasurableSpace A] {μ : Measure A}
    (W : A → TFLq (volume.restrict Ω)) (hW : AEStronglyMeasurable W μ) (y : Space) :
    AEStronglyMeasurable (fun x => tfPotential (localTFMinimizer hΩ (W x)) y) μ :=
  (continuous_tfPotential_evaluation hΩ y).comp_aestronglyMeasurable
    ((continuous_localTFMinimizer hΩ).comp_aestronglyMeasurable hW)

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_CorePointMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma potentialForm_coreSlice_point_aestronglyMeasurable {m k : ℕ}
    (u : H1Vector (m+k)) (s : Spins m)
    (W : Configuration m × Configuration k → ℝ) (hW : Measurable W) :
    AEStronglyMeasurable (fun x => potentialForm (fun v => W (x,v)) (u.coreSlice s x)) volume := by
  apply AEStronglyMeasurable.congr _
    (show (fun x => ∑ t : Spins k, ∫ v, W (x,v)*
      ‖u.value (Fin.append s t) (joinConfiguration m k (x,v))‖^2) =ᵐ[volume]
      (fun x => potentialForm (fun v => W (x,v)) (u.coreSlice s x)) from ?_)
  · apply Finset.aestronglyMeasurable_fun_sum
    intro t ht
    have hψ := ((u.value_L2 (Fin.append s t)).aestronglyMeasurable.comp_measurePreserving
      (joinConfiguration_measurePreserving m k)).norm.pow 2
    exact (hW.aestronglyMeasurable.mul hψ).integral_prod_right'
  · filter_upwards [u.coreSliceRegular_ae s] with x hx
    simp only [potentialForm,u.coreSlice_value s hx]

lemma coreScreenedField_slice_point_aestronglyMeasurable {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) (s : Spins m) (y : Space) :
    AEStronglyMeasurable (fun x => coreScreenedField S (u.coreSlice s x).normalized y) volume := by
  have hw : Measurable (fun z : Configuration m × Configuration k => restrictedOutPotential z.2 Set.univ y) := by
    apply Finset.measurable_fun_sum
    intro i hi
    simp only [Set.mem_univ,ite_true,coulombKernel]
    exact (((continuous_position i).measurable.comp measurable_snd).sub measurable_const).norm.inv
  have H := potentialForm_coreSlice_point_aestronglyMeasurable u s _ hw
  have H' : AEStronglyMeasurable (fun x : Configuration m =>
      (mass (u.coreSlice s x))⁻¹*potentialForm (fun v => restrictedOutPotential v Set.univ y)
        (u.coreSlice s x)) volume :=
    (mass_coreSlice_integrable u s).aestronglyMeasurable.inv₀.mul H
  have H'' : AEStronglyMeasurable (fun x => coreCoulombPotential (u.coreSlice s x).normalized y) volume := by
    apply H'.congr
    filter_upwards [] with x
    symm
    rw [←potentialForm_normalized_eq,potentialForm_restrictedOutPotential _ MeasurableSet.univ]
    simp only [restrictedCorePotential,Set.mem_univ,ite_true,coreCoulombPotential]
  exact aestronglyMeasurable_const.sub H''

lemma patchTFScreenedField_slice_aestronglyMeasurable {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) (s : Spins m) {a b t : ℝ} (ha : 0<a) (hb : 0<b)
    (ht : t≤6*a) (y : Space) (hn : ∀ j, 20*a≤‖S.position j-y‖) (z : Space) :
    AEStronglyMeasurable (fun x => patchTFScreenedField S (u.coreSlice s x).normalized ha hb ht y hn z) volume := by
  exact (coreScreenedField_slice_point_aestronglyMeasurable S u s z).sub
    (aestronglyMeasurable_localTFPotential measurableSet_ball _
      (coreTFField_slice_aestronglyMeasurable S u s measurableSet_ball ha
        (patch_nucleus_separation S ha hb ht y hn)) z)

end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma ae_position_ne (n : ℕ) (y : Space) : ∀ᵐ x : Configuration n,∀ i,position x i≠y := by
  rw [ae_all_iff]
  intro i
  let L : Configuration n →ₗ[ℝ] ℝ :=
    { toFun := fun x => x (i,0)
      map_add' := by intro x z; rfl
      map_smul' := by intro c x; rfl }
  have hL : LinearMap.ker L≠⊤ := by
    intro h
    have hh : EuclideanSpace.single (i,0) (1:ℝ)∈LinearMap.ker L := by rw [h]; trivial
    change (EuclideanSpace.single (i,0) (1:ℝ)) (i,0)=0 at hh
    simp at hh
  let v : Configuration n := EuclideanSpace.single (i,0) (y 0)
  have hv : v (i,0)=y 0 := by simp [v]
  have hz := Measure.addHaar_submodule (volume : Measure (Configuration n)) (LinearMap.ker L) hL
  have hnull : (volume : Measure (Configuration n)) {x | position x i=y}=0 := by
    apply measure_mono_null (t := (fun x : Configuration n => x+(-v)) ⁻¹' (LinearMap.ker L : Set (Configuration n)))
    · intro x hx
      change (x+(-v)) (i,0)=0
      simp only [PiLp.add_apply,PiLp.neg_apply,hv]
      have hs := congrArg (fun z : Space => z 0) hx
      change x (i,0)=y 0 at hs
      rw [hs,add_neg_cancel]
    · rw [measure_preimage_add_right,hz]
  rw [ae_iff]
  simpa only [not_not] using hnull

lemma patchFieldTransferError_aestronglyMeasurable {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (ht : t≤6*a) (y : Space)
    (hn : ∀ j,20*a≤‖S.position j-y‖) (s : Spins m) :
    AEStronglyMeasurable (patchFieldTransferError S u ha hb ht y hn s) volume := by
  have hnuc : Measurable (nuclearPotential (n := m) (unitNucleus y)) :=
    Finset.measurable_sum _ (fun i _ => (attraction_measurable _).comp (continuous_position i).measurable)
  exact ((coreScreenedField_slice_point_aestronglyMeasurable S u s y).sub hnuc.aestronglyMeasurable).sub
    (patchTFScreenedField_slice_aestronglyMeasurable S u s ha hb ht y hn y)

lemma patchTransferRemainder_weight_integrable {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (ht : t≤6*a) (y : Space)
    (hn : ∀ j,20*a≤‖S.position j-y‖) (r ε : ℝ) (s : Spins m)
    (hcs : ∀ᵐ x, SpatiallySupported (u.coreSlice s x).normalized {z | t≤‖z-y‖}) :
    Integrable (fun x => mass (u.coreSlice s x)*patchTransferRemainder S u ha hb ht y hn r ε s x) := by
  have hgap := (patchSliceTFGap_weight_integrable S u ha hb ht y hn s hcs).const_mul (5/(4*r*ε))
  have hnear (R : ℝ) := slice_weight_integrable_const u (nearPotential y R)
    (nearPotential_outer_integrable u y R) s
  have hcount := (sliceCount_weight_integrable u (A := {z | t-7*b≤‖z-y‖})
    (isClosed_le continuous_const (by fun_prop : Continuous (fun z : Space => ‖z-y‖))).measurableSet s 1).div_const a
  simp only [pow_one] at hcount
  have hε := (mass_coreSlice_integrable u s).mul_const ε
  have hC := (mass_coreSlice_integrable u s).mul_const
    (((tfInteriorConstant thomasFermiKineticConstant/
      (thomasFermiKineticConstant*(5/3:ℝ)))^(3/2:ℝ)/a^6)*(2*Real.pi*r^2))
  apply (((((hε.add hgap).add (hnear (r+2*b))).add (hnear (2*b))).add hcount).add hC).congr
  exact Eventually.of_forall (fun x => by dsimp only [Pi.add_apply]; unfold patchTransferRemainder; ring)

lemma patchFieldTransferError_ae_bound {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t r ε : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
    (hn : ∀ j,20*a≤‖S.position j-y‖) (hr : 0 < r) (hra : r≤a) (hε : 0<ε) (s : Spins m)
    (hcs : ∀ᵐ x, SpatiallySupported (u.coreSlice s x).normalized {z | t≤‖z-y‖}) :
    ∀ᵐ x, |patchFieldTransferError S u ha hb ht.2 y hn s x|≤
      patchTransferRemainder S u ha hb ht.2 y hn r ε s x := by
  filter_upwards [ae_position_ne m y,hcs] with x hxy hcore
  have hh := patch_raw_field_transfer S u ha hb hsmall ht y hn hr hra s x hcore hxy
  have hyoung := sqrt_young ((5/r)*patchSliceTFGap S u ha hb ht.2 y hn s x)
    (mul_nonneg (by positivity) (patchSliceTFGap_nonneg S u ha hb ht.2 y hn s x)) hε
  have he : ((5/r)*patchSliceTFGap S u ha hb ht.2 y hn s x)/(4*ε)=
      (5/(4*r*ε))*patchSliceTFGap S u ha hb ht.2 y hn s x := by ring
  rw [he] at hyoung
  rw [deletedLabels_patchRetained] at hh
  change |_ - _|≤_
  unfold patchTransferRemainder
  linarith

theorem patchFieldTransferError_integrable_mean {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t r ε : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
    (hn : ∀ j,20*a≤‖S.position j-y‖) (hr : 0 < r) (hra : r≤a) (hε : 0<ε)
    (hcs : ∀ s, ∀ᵐ x, SpatiallySupported (u.coreSlice s x).normalized {z | t≤‖z-y‖}) :
    (∀ s, Integrable (fun x => mass (u.coreSlice s x)*patchFieldTransferError S u ha hb ht.2 y hn s x)) ∧
    |sliceExpectation u (patchFieldTransferError S u ha hb ht.2 y hn)|≤
      sliceExpectation u (patchTransferRemainder S u ha hb ht.2 y hn r ε) := by
  have hR := fun s => patchTransferRemainder_weight_integrable S u ha hb ht.2 y hn r ε s (hcs s)
  have hB := fun s => patchFieldTransferError_ae_bound S u ha hb hsmall ht y hn hr hra hε s (hcs s)
  have hI (s) : Integrable (fun x => mass (u.coreSlice s x)*patchFieldTransferError S u ha hb ht.2 y hn s x) := by
    apply (hR s).mono' ((mass_coreSlice_integrable u s).aestronglyMeasurable.mul
      (patchFieldTransferError_aestronglyMeasurable S u ha hb ht.2 y hn s))
    filter_upwards [hB s] with x hx
    dsimp only [Pi.mul_apply]
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (mass_nonneg _)]
    exact mul_le_mul_of_nonneg_left hx (mass_nonneg _)
  refine ⟨hI,?_⟩
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro s _
  apply abs_integral_le_integral_abs.trans
  apply integral_mono_ae (hI s).abs (hR s)
  filter_upwards [hB s] with x hx
  rw [abs_mul,abs_of_nonneg (mass_nonneg _)]
  exact mul_le_mul_of_nonneg_left hx (mass_nonneg _)
end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_EnsembleTransfer
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
namespace Coulomb

lemma sliceExpectation_linear_remainder {m k : ℕ} (u : H1Vector (m+k))
    (G N₁ N₂ D : Spins m → Configuration m → ℝ) (c ε C a : ℝ)
    (hG : ∀ s,Integrable (fun x => mass (u.coreSlice s x)*G s x))
    (hN₁ : ∀ s,Integrable (fun x => mass (u.coreSlice s x)*N₁ s x))
    (hN₂ : ∀ s,Integrable (fun x => mass (u.coreSlice s x)*N₂ s x))
    (hD : ∀ s,Integrable (fun x => mass (u.coreSlice s x)*D s x)) :
    sliceExpectation u (fun s x => ε+c*G s x+N₁ s x+N₂ s x+D s x/a+C)=
      ε*mass u+c*sliceExpectation u G+sliceExpectation u N₁+sliceExpectation u N₂+
        sliceExpectation u D/a+C*mass u := by
  have he (s : Spins m) :
      (∫ x,mass (u.coreSlice s x)*(ε+c*G s x+N₁ s x+N₂ s x+D s x/a+C))=
        ε*(∫ x,mass (u.coreSlice s x))+c*(∫ x,mass (u.coreSlice s x)*G s x)+
        (∫ x,mass (u.coreSlice s x)*N₁ s x)+(∫ x,mass (u.coreSlice s x)*N₂ s x)+
        (∫ x,mass (u.coreSlice s x)*D s x)/a+C*(∫ x,mass (u.coreSlice s x)) := by
    have h0 := (mass_coreSlice_integrable u s).const_mul ε
    have h1 := (hG s).const_mul c
    have hd := (hD s).div_const a
    have hC := (mass_coreSlice_integrable u s).const_mul C
    calc
      _=(∫ x,ε*mass (u.coreSlice s x)+c*(mass (u.coreSlice s x)*G s x)+
        mass (u.coreSlice s x)*N₁ s x+mass (u.coreSlice s x)*N₂ s x+
        (mass (u.coreSlice s x)*D s x)/a+C*mass (u.coreSlice s x)) := by
          apply integral_congr_ae
          exact Eventually.of_forall (fun x => by ring)
      _=_ := by
        have hA := integral_add ((((h0.add h1).add (hN₁ s)).add (hN₂ s)).add hd) hC
        have hB := integral_add (((h0.add h1).add (hN₁ s)).add (hN₂ s)) hd
        have hE := integral_add ((h0.add h1).add (hN₁ s)) (hN₂ s)
        have hF := integral_add (h0.add h1) (hN₁ s)
        have hH := integral_add h0 h1
        simp only [Pi.add_apply] at hA hB hE hF hH
        rw [hA,hB,hE,hF,hH,integral_const_mul,integral_const_mul,integral_const_mul,integral_div]
  unfold sliceExpectation
  simp only [he,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_div,integral_mass_coreSlice]

lemma nearPotential_fresh_expectation {n : ℕ} (T : RecordedEnsemble n) (u : H1Vector n)
    (hT : T.Conserves u) {y : Space} {R t : ℝ} (hs : T.CoreSupported {z | t≤‖z-y‖}) (hRt : R≤t) :
    (∑ p,sliceExpectation (T.vector p) (fun _ x => nearPotential y R x))=
      potentialForm (nearPotential y R) u := by
  rw [←hT.nearPotential y R]
  apply Finset.sum_congr rfl
  intro p _
  rw [sliceExpectation_const (T.vector p) _ (nearPotential_outer_integrable (T.vector p) y R)]
  exact (supported_core_nearPotential (T.vector p) y hRt (hs p)).symm

lemma fresh_deleted_mean_le {n : ℕ} (T : RecordedEnsemble n)
    (hm : (∑ p,mass (T.vector p))=1) (y : Space) (t b : ℝ) :
    (∑ p,sliceExpectation (T.vector p) (fun _ x => localCount {z | t-7*b≤‖z-y‖} x))≤
      Real.sqrt (T.deletedSquare y t b) := by
  apply slice_ensemble_mean_le_sqrt T.out T.core T.vector _ _ _ _ hm
  · exact fun p s => (localCount_measurable (isClosed_le continuous_const (by fun_prop)).measurableSet).aestronglyMeasurable
  · exact fun p s => Eventually.of_forall (fun x => localCount_nonneg _ x)
  · exact fun p s => sliceCount_weight_integrable (T.vector p)
      (isClosed_le continuous_const (by fun_prop)).measurableSet s 2

theorem ensemble_patch_error_bound {J n : ℕ} (S : Nuclei J) (T : RecordedEnsemble n) (u : H1Vector n)
    (hT : T.Conserves u) (hm : (∑ p,mass (T.vector p))=1)
    {a b t r ε : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
    (hn : ∀ j,20*a≤‖S.position j-y‖) (hr : 0 < r) (hra : r≤a) (hε : 0<ε)
    (hcs : T.CoreSupported {z | t≤‖z-y‖}) :
    |∑ p,sliceExpectation (T.vector p) (patchFieldTransferError S (T.vector p) ha hb ht.2 y hn)|≤
      ε+(5/(4*r*ε))*(∑ p,sliceExpectation (T.vector p) (patchSliceTFGap S (T.vector p) ha hb ht.2 y hn))+
      potentialForm (nearPotential y (r+2*b)) u+potentialForm (nearPotential y (2*b)) u+
      Real.sqrt (T.deletedSquare y t b)/a+
      ((tfInteriorConstant thomasFermiKineticConstant/
        (thomasFermiKineticConstant*(5/3:ℝ)))^(3/2:ℝ)/a^6)*(2*Real.pi*r^2) := by
  have hs (p : T.index) (s) : ∀ᵐ x, SpatiallySupported ((T.vector p).coreSlice s x).normalized {z | t≤‖z-y‖} :=
    ((hcs p).coreSlice s).mono (fun x hx => hx.normalized)
  have HB := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun p (_ : p∈Finset.univ) =>
    (patchFieldTransferError_integrable_mean S (T.vector p) ha hb hsmall ht y hn hr hra hε (hs p)).2))
  have HE (p : T.index) :
      sliceExpectation (T.vector p) (patchTransferRemainder S (T.vector p) ha hb ht.2 y hn r ε)=
        ε*mass (T.vector p)+(5/(4*r*ε))*sliceExpectation (T.vector p) (patchSliceTFGap S (T.vector p) ha hb ht.2 y hn)+
        sliceExpectation (T.vector p) (fun _ x => nearPotential y (r+2*b) x)+
        sliceExpectation (T.vector p) (fun _ x => nearPotential y (2*b) x)+
        sliceExpectation (T.vector p) (fun _ x => localCount {z | t-7*b≤‖z-y‖} x)/a+
        (((tfInteriorConstant thomasFermiKineticConstant/
          (thomasFermiKineticConstant*(5/3:ℝ)))^(3/2:ℝ)/a^6)*(2*Real.pi*r^2))*mass (T.vector p) := by
    apply sliceExpectation_linear_remainder
    · exact fun s => patchSliceTFGap_weight_integrable S (T.vector p) ha hb ht.2 y hn s (hs p s)
    · exact fun s => slice_weight_integrable_const (T.vector p) _ (nearPotential_outer_integrable (T.vector p) y (r+2*b)) s
    · exact fun s => slice_weight_integrable_const (T.vector p) _ (nearPotential_outer_integrable (T.vector p) y (2*b)) s
    · intro s
      simpa only [pow_one] using sliceCount_weight_integrable (T.vector p)
        (isClosed_le continuous_const (by fun_prop)).measurableSet s 1
  simp only [HE,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_div,hm,mul_one] at HB
  rw [nearPotential_fresh_expectation T u hT hcs (by linarith [ht.1] : r+2*b≤t),
    nearPotential_fresh_expectation T u hT hcs (by linarith [ht.1] : 2*b≤t)] at HB
  have hD := div_le_div_of_nonneg_right (fresh_deleted_mean_le T hm y t b) ha.le
  linarith
end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FreshFieldTransfer
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
namespace Coulomb

lemma fresh_raw_coulomb_weight_integrable {m k : ℕ} (u : H1Vector (m+k)) (y : Space) (s : Spins m) :
    Integrable (fun x => mass (u.coreSlice s x)*(coreCoulombPotential (u.coreSlice s x).normalized y+
      nuclearPotential (unitNucleus y) x)) := by
  have hc : Integrable (fun x => mass (u.coreSlice s x)*coreCoulombPotential (u.coreSlice s x).normalized y) := by
    simp only [←nuclearEnergy_unit_eq_coreCoulomb]
    change Integrable (fun x => mass (u.coreSlice s x)*potentialForm (nuclearPotential (unitNucleus y))
      (u.coreSlice s x).normalized)
    simp_rw [potentialForm_normalized_weight]
    exact potentialForm_coreSlice_integrable u s _ (fun t => u.core_nuclear_integrable (unitNucleus y) (Fin.append s t))
  have ho := slice_weight_integrable_const u (nuclearPotential (unitNucleus y))
    (u.outer_nuclear_integrable (unitNucleus y)) s
  apply (hc.add ho).congr
  exact Eventually.of_forall (fun x => by dsimp only [Pi.add_apply]; rw [mul_add])

lemma fresh_raw_screened_weight_integrable {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) (y : Space) (s : Spins m) :
    Integrable (fun x => mass (u.coreSlice s x)*(coreScreenedField S (u.coreSlice s x).normalized y-
      nuclearPotential (unitNucleus y) x)) := by
  apply (((mass_coreSlice_integrable u s).mul_const (attraction S y)).sub
    (fresh_raw_coulomb_weight_integrable u y s)).congr
  exact Eventually.of_forall (fun x => by dsimp only [Pi.sub_apply]; unfold coreScreenedField; ring)

lemma fresh_raw_screened_tower {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k)) (y : Space) :
    sliceExpectation u (fun s x => coreScreenedField S (u.coreSlice s x).normalized y-
      nuclearPotential (unitNucleus y) x)=attraction S y*mass u-coreCoulombPotential u y := by
  have he : (fun s x => coreScreenedField S (u.coreSlice s x).normalized y-nuclearPotential (unitNucleus y) x)=
      fun s x => attraction S y-(coreCoulombPotential (u.coreSlice s x).normalized y+nuclearPotential (unitNucleus y) x) := by
    funext s x
    unfold coreScreenedField
    ring
  rw [he,sliceExpectation_sub u _ _ (fun s => (mass_coreSlice_integrable u s).mul_const _)
    (fresh_raw_coulomb_weight_integrable u y),sliceExpectation_number,fresh_core_coulomb_tower]

theorem patchTFScreenedField_weight_integrable {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t r ε : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
    (hn : ∀ j,20*a≤‖S.position j-y‖) (hr : 0 < r) (hra : r≤a) (hε : 0<ε)
    (hcs : ∀ s, ∀ᵐ x, SpatiallySupported (u.coreSlice s x).normalized {z | t≤‖z-y‖}) (s : Spins m) :
    Integrable (fun x => mass (u.coreSlice s x)*patchTFScreenedField S (u.coreSlice s x).normalized ha hb ht.2 y hn y) := by
  have hE := (patchFieldTransferError_integrable_mean S u ha hb hsmall ht y hn hr hra hε hcs).1 s
  apply ((fresh_raw_screened_weight_integrable S u y s).sub hE).congr
  exact Eventually.of_forall (fun x => by dsimp only [Pi.sub_apply]; unfold patchFieldTransferError; ring)

theorem fresh_patch_field_tower {J n : ℕ} (S : Nuclei J) (T : RecordedEnsemble n) (u : H1Vector n)
    (hT : T.Conserves u) (hm : (∑ p,mass (T.vector p))=1)
    {a b t r ε : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
    (hn : ∀ j,20*a≤‖S.position j-y‖) (hr : 0 < r) (hra : r≤a) (hε : 0<ε)
    (hcs : T.CoreSupported {z | t≤‖z-y‖}) :
    (∑ p,sliceExpectation (T.vector p) (patchFieldTransferError S (T.vector p) ha hb ht.2 y hn))=
      coreScreenedField S u y-(∑ p,sliceExpectation (T.vector p) (fun s x =>
        patchTFScreenedField S ((T.vector p).coreSlice s x).normalized ha hb ht.2 y hn y)) := by
  have hs (p : T.index) (s) : ∀ᵐ x, SpatiallySupported ((T.vector p).coreSlice s x).normalized {z | t≤‖z-y‖} :=
    ((hcs p).coreSlice s).mono (fun x hx => hx.normalized)
  have he (p : T.index) :
      sliceExpectation (T.vector p) (patchFieldTransferError S (T.vector p) ha hb ht.2 y hn)=
      attraction S y*mass (T.vector p)-coreCoulombPotential (T.vector p) y-
      sliceExpectation (T.vector p) (fun s x => patchTFScreenedField S ((T.vector p).coreSlice s x).normalized ha hb ht.2 y hn y) := by
    unfold patchFieldTransferError
    rw [sliceExpectation_sub (T.vector p) _ _ (fresh_raw_screened_weight_integrable S (T.vector p) y)
      (patchTFScreenedField_weight_integrable S (T.vector p) ha hb hsmall ht y hn hr hra hε (hs p)),
      fresh_raw_screened_tower]
  simp only [he,Finset.sum_sub_distrib,←Finset.mul_sum,hm,mul_one,hT.coulomb_potential y,coreScreenedField]

theorem fresh_patch_field_transfer {J n : ℕ} (S : Nuclei J) (T : RecordedEnsemble n) (u : H1Vector n)
    (hT : T.Conserves u) (hm : (∑ p,mass (T.vector p))=1)
    {a b t r ε : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
    (hn : ∀ j,20*a≤‖S.position j-y‖) (hr : 0 < r) (hra : r≤a) (hε : 0<ε)
    (hcs : T.CoreSupported {z | t≤‖z-y‖}) :
    |coreScreenedField S u y-(∑ p,sliceExpectation (T.vector p) (fun s x =>
      patchTFScreenedField S ((T.vector p).coreSlice s x).normalized ha hb ht.2 y hn y))|≤
      ε+(5/(4*r*ε))*(∑ p,sliceExpectation (T.vector p) (patchSliceTFGap S (T.vector p) ha hb ht.2 y hn))+
      potentialForm (nearPotential y (r+2*b)) u+potentialForm (nearPotential y (2*b)) u+
      Real.sqrt (T.deletedSquare y t b)/a+
      ((tfInteriorConstant thomasFermiKineticConstant/
        (thomasFermiKineticConstant*(5/3:ℝ)))^(3/2:ℝ)/a^6)*(2*Real.pi*r^2) := by
  rw [←fresh_patch_field_tower S T u hT hm ha hb hsmall ht y hn hr hra hε hcs]
  exact ensemble_patch_error_bound S T u hT hm ha hb hsmall ht y hn hr hra hε hcs
end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_AtomicRetainedGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

theorem exists_atomic_physical_gap_with_deleted {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hψ : Antisymmetric ψ) (hm : mass ψ=1)
    {E δ : ℝ} (hE : (E:EReal)≤unrestrictedFormBottom S) (hstate : form S ψ≤E+δ)
    (hδ : 0≤δ) {y : Space} (hy : y≠0) {b : ℝ} (hb : 0<b)
    (hsmall : 18*b≤atomicCellScale y)
    (hcond : atomicCellScale y≤b^2*Real.sqrt (screenCountParameter ψ δ)*screenMass δ (atomicCellScale y)) :
    ∃ t : ℝ, ∃ ht : t∈Set.Icc (5*atomicCellScale y) (6*atomicCellScale y),
    ∃ T : AtomicBudgetHistory S ψ (thinIMS ψ y t b) 1,
      T.ensemble.totalForm S≤form S ψ+thinIMS ψ y t b ∧
      T.ensemble.OutFermionic ∧ T.ensemble.CoreSupported {z | t≤‖z-y‖} ∧
      T.ensemble.OutSupported (Metric.closedBall y (t+b)) ∧
      atomicPatchTFGap S hatom T.ensemble y hy b hb t ht.2 ≤
        atomicRefinedError δ (screenCountParameter ψ δ) (atomicCellScale y) b ∧
      T.ensemble.deletedSquare y t b ≤
        18*atomicPatchCountFactor*(b/atomicCellScale y)*(screenCountParameter ψ δ)*(screenMass δ (atomicCellScale y))^2 := by
  let a := atomicCellScale y
  let P := screenCountParameter ψ δ
  let m := screenMass δ a
  have ha : 0<a := atomicCellScale_pos hy
  have hP1 : 1≤P := screenCountParameter_ge_one ψ δ
  have hP : 0≤P := le_trans zero_le_one hP1
  have hm0 : 0 < m := screenMass_pos δ a
  have hc := fun z hz => screenCountParameter_controls ψ hm δ (y:=z) hz
  obtain ⟨t,ht,T,hEt,ho,hcs,hos,hD,hN,hraw⟩ :=
    exists_atomic_thin_screened_sharp S hatom ψ hψ hm hE hstate hδ hy hb hsmall hcond
  let F := fun p s x => atomicPatchCap S ((T.ensemble.vector p).coreSlice s x).normalized x y
  let Q := ∑ p, sliceExpectation (T.ensemble.vector p) (fun s x => (F p s x)^2)
  let N := ∑ p, (T.ensemble.out p:ℝ)^2*mass (T.ensemble.vector p)
  have hN0 : 0≤N := Finset.sum_nonneg (fun p _ => mul_nonneg (sq_nonneg _) (mass_nonneg _))
  have hD0 : 0≤T.ensemble.deletedSquare y t b := Finset.sum_nonneg (fun p _ =>
    Finset.sum_nonneg (fun s _ => integral_nonneg (fun x => mul_nonneg (mass_nonneg _) (sq_nonneg _))))
  have hwidth : t+b≤80*a := by dsimp only [a] at *; linarith [ht.2]
  have hgap : T.ensemble.totalForm S≤E+(δ+thinIMS ψ y t b) := by linarith
  have hQ : Q≤atomicPhysicalCapConstant*P*m^2/a^2 := by
    have HQ := atomicPatchCap_ensemble_square S hatom T.ensemble hy
      (H := (2*atomicBudgetRecursionC^3*Real.sqrt thinReserveFactor*screenFieldUnit δ P a)^2)
      (fun v hv => (Real.sqrt_le_iff.mp (hraw v hv)).2)
    change Q≤_ at HQ
    calc
      Q≤16*(Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*
        (2*atomicBudgetRecursionC^3*Real.sqrt thinReserveFactor*screenFieldUnit δ P a)^2+8*N/(9*a^2) := HQ
      _≤16*(Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*
        (2*atomicBudgetRecursionC^3*Real.sqrt thinReserveFactor*screenFieldUnit δ P a)^2+
        8*(atomicPatchCountFactor*P*m^2)/(9*a^2) := add_le_add le_rfl
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hN (by norm_num)) (by positivity))
      _=atomicPhysicalCapConstant*P*m^2/a^2 := by
        dsimp only [atomicPhysicalCapConstant,screenFieldUnit,m]
        simp only [mul_pow,div_pow,Real.sq_sqrt hP]
        ring
  have hQ0 : 0≤atomicPhysicalCapConstant*P*m^2/a^2 := by positivity [atomicPhysicalCapConstant_nonneg]
  have hn (j) : 20*a≤‖S.position j-y‖ := by
    rw [hatom j,zero_sub,norm_neg]
    dsimp only [a,atomicCellScale]
    nlinarith [norm_nonneg y]
  have hH := physical_ensemble_gap S ψ T.ensemble T.law T.fermionic ho
    (T.mass_eq.trans hm) hE hgap ha hb hsmall ht y hn hcs hos F
    (fun p s => atomicPatchCap_slice_aestronglyMeasurable S (T.ensemble.vector p) s y)
    (fun p s => Eventually.of_forall (fun x => atomicPatchCap_nonneg S _ x hy))
    (fun p s => atomicPatchCap_weight_integrable S hatom (T.ensemble.vector p) s hy)
    (fun p s => Eventually.of_forall (fun x w hw => coreField_le_atomicPatchCap S hatom _ x hy
      ((show ‖w-y‖≤t+b from by simpa only [Metric.mem_closedBall,dist_eq_norm] using hw).trans hwidth)))
  refine ⟨t,ht,T,hEt,ho,hcs,hos,?_,hD⟩
  change atomicPatchTFGap S hatom T.ensemble y hy b hb t ht.2≤_ at hH
  apply hH.trans
  unfold atomicRefinedError
  have hB := thinIMS_sharp_budget ψ hm hδ hP hc hy hb hwidth
  have hp := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hQ)
    (show 0≤12*a*unitWindowKinetic/b^2 from div_nonneg (mul_nonneg (by positivity) unitWindowKinetic_nonneg) (sq_nonneg _))
  have hd := Real.sqrt_le_sqrt (mul_le_mul hQ hD hD0 hQ0)
  have hf := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hN0 hN (by norm_num : (0:ℝ)≤2/3))
    (show 0≤(b⁻¹)^2*((Real.pi^2/2)*neumannBoundary) by positivity [neumannBoundary_nonneg])
  have hn' := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hN)
    (show 0≤(2*Real.pi+1)/(2*b) by positivity [Real.pi_pos])
  dsimp only [Q,N,m,a,P] at hp hd hf hn' hB ⊢
  linarith

end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma atomic_deleted_small_bound {δ P a : ℝ} (hδ : 0≤δ) (hP : 0≤P)
    (hPP : P≤atomicCountConstant) (ha : 0<a) (ha1 : a≤1) (hd : δ≤a^(-349/50:ℝ)) :
    18*atomicPatchCountFactor*(a^(6/5:ℝ)/a)*P*(screenMass δ a)^2 ≤
      (72*atomicPatchCountFactor*atomicCountConstant)*a^(-29/5:ℝ) := by
  have hsmall : δ*a^7≤1 := by
    calc
      δ*a^7≤a^(-349/50:ℝ)*a^7 := mul_le_mul_of_nonneg_right hd (pow_nonneg ha.le _)
      _=a^(1/50:ℝ) := by rw [←Real.rpow_natCast a 7,←Real.rpow_add ha]; norm_num
      _≤1 := Real.rpow_le_one ha.le ha1 (by norm_num)
  have hm := NeutralAtom.screenMass_small_offset ha ha1 hδ hsmall
  have hm' : screenMass δ a≤2*a^(-3:ℝ) := by
    simpa only [Real.rpow_neg ha.le,Real.rpow_ofNat,div_eq_mul_inv] using hm
  have hA := atomicPatchCountFactor_nonneg
  have hC : 0≤atomicCountConstant := hP.trans hPP
  calc
    _≤18*atomicPatchCountFactor*(a^(6/5:ℝ)/a)*atomicCountConstant*(2*a^(-3:ℝ))^2 := by
      gcongr
      exact (screenMass_pos _ _).le
    _=(72*atomicPatchCountFactor*atomicCountConstant)*a^(-29/5:ℝ) := by
      have hm2 : (2*a^(-3:ℝ))^2=4*a^(-6:ℝ) := by
        rw [mul_pow,←Real.rpow_mul_natCast ha.le]
        norm_num
      rw [hm2]
      calc
        _=((72*atomicPatchCountFactor*atomicCountConstant)*(a^(6/5:ℝ)*a^(-6:ℝ)))/a^1 := by ring
        _=_ := by rw [←Real.rpow_add ha,←Real.rpow_natCast a 1,div_rpow_monomial ha]; norm_num

theorem exists_atomic_small_gap_with_deleted : ∃ s : ℝ, 0 < s ∧ s≤1 ∧
    ∀ {J n : ℕ} (S : Nuclei J) (hatom : ∀ i, S.position i=0)
    (ψ : H1Vector n), Antisymmetric ψ → mass ψ=1 →
    ∀ {E δ : ℝ}, (E:EReal)≤unrestrictedFormBottom S → form S ψ≤E+δ → 0≤δ →
    ∀ (y : Space) (hy : y≠0), atomicCellScale y < s → δ≤(atomicCellScale y)^(-349/50:ℝ) →
    ∃ t : ℝ, ∃ ht : t∈Set.Icc (5*atomicCellScale y) (6*atomicCellScale y),
    ∃ T : AtomicBudgetHistory S ψ (thinIMS ψ y t ((atomicCellScale y)^(6/5:ℝ))) 1,
      T.ensemble.totalForm S≤form S ψ+thinIMS ψ y t ((atomicCellScale y)^(6/5:ℝ)) ∧
      T.ensemble.OutFermionic ∧ T.ensemble.CoreSupported {z | t≤‖z-y‖} ∧
      T.ensemble.OutSupported (Metric.closedBall y (t+(atomicCellScale y)^(6/5:ℝ))) ∧
      atomicPatchTFGap S hatom T.ensemble y hy ((atomicCellScale y)^(6/5:ℝ))
        (Real.rpow_pos_of_pos (atomicCellScale_pos hy) _) t ht.2≤2*(atomicCellScale y)^(-349/50:ℝ) ∧
      T.ensemble.deletedSquare y t ((atomicCellScale y)^(6/5:ℝ))≤
        (72*atomicPatchCountFactor*atomicCountConstant)*(atomicCellScale y)^(-29/5:ℝ) := by
  obtain ⟨s,hs,hs1,hbound⟩ := exists_atomic_refined_small_scale
  refine ⟨s,hs,hs1,?_⟩
  intro J n S hatom ψ hψ hm E δ hE hstate hδ y hy hys hd
  let a := atomicCellScale y
  have ha : 0<a := atomicCellScale_pos hy
  have ha1 : a≤1 := hys.le.trans hs1
  obtain ⟨hsmall,herror⟩ := hbound a ha hys
  obtain ⟨t,ht,T,hT,ho,hcs,hos,hgap,hD⟩ := exists_atomic_physical_gap_with_deleted S hatom ψ hψ hm hE hstate hδ
    hy (Real.rpow_pos_of_pos ha (6/5:ℝ)) hsmall
    (source_patch_scale_condition ha ha1 (screenCountParameter_ge_one ψ δ))
  have hPP := screenCountParameter_le_atomicCountConstant S hatom ψ hψ hm hE hstate hδ
  have hP := le_trans zero_le_one (screenCountParameter_ge_one ψ δ)
  refine ⟨t,ht,T,hT,ho,hcs,hos,?_,?_⟩
  · exact hgap.trans ((atomicRefinedError_small_bound hδ hP hPP ha ha1 hd).trans herror)
  · exact hD.trans (atomic_deleted_small_bound hδ hP hPP ha ha1 hd)
end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FreshTransferScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma transfer_radius_le {a : ℝ} (ha : 0<a) (ha1 : a≤1) :
    a^(6/5:ℝ)≤a^(101/100:ℝ) ∧ a^(101/100:ℝ)≤a := by
  exact ⟨Real.rpow_le_rpow_of_exponent_ge ha ha1 (by norm_num),
    by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge ha ha1 (by norm_num : (1:ℝ)≤101/100)⟩

lemma transfer_near_power {a : ℝ} (ha : 0<a) {R : ℝ}
    (hR : 0≤R) (hRb : R≤3*a^(101/100:ℝ)) (C : ℝ) (hC : 0≤C) :
    C*a^(-21/5:ℝ)*R^(1/5:ℝ)≤(C*3^(1/5:ℝ))*a^(-1999/500:ℝ) := by
  calc
    _≤C*a^(-21/5:ℝ)*(3*a^(101/100:ℝ))^(1/5:ℝ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hR hRb (by norm_num)) (by positivity)
    _=(C*3^(1/5:ℝ))*a^(-1999/500:ℝ) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤3) (Real.rpow_nonneg ha.le _),←Real.rpow_mul ha.le]
      calc
        _=(C*3^(1/5:ℝ))*(a^(-21/5:ℝ)*a^((101/100)*(1/5):ℝ)) := by ring
        _=_ := by rw [←Real.rpow_add ha]; norm_num

lemma transfer_gap_power {a : ℝ} (ha : 0<a) :
    a^(-799/200:ℝ)+(5/(4*a^(101/100:ℝ)*a^(-799/200:ℝ)))*(2*a^(-349/50:ℝ))=
      (7/2:ℝ)*a^(-799/200:ℝ) := by
  have he : (5/(4*a^(101/100:ℝ)*a^(-799/200:ℝ)))*(2*a^(-349/50:ℝ))=
      (5/2:ℝ)*a^(-799/200:ℝ) := by
    calc
      _=((5/2:ℝ)*a^(-349/50:ℝ))/(a^(101/100:ℝ)*a^(-799/200:ℝ)) := by ring
      _=_ := by rw [←Real.rpow_add ha,div_rpow_monomial ha]; norm_num
  rw [he]
  ring

lemma transfer_deleted_power {a C : ℝ} (ha : 0<a) (hC : 0≤C) :
    Real.sqrt (C*a^(-29/5:ℝ))/a=Real.sqrt C*a^(-39/10:ℝ) := by
  rw [sqrt_rpow_monomial ha hC]
  conv_lhs => arg 2; rw [←Real.rpow_one a]
  rw [div_rpow_monomial ha]
  norm_num

lemma transfer_tfnear_power {a : ℝ} (ha : 0<a) (K : ℝ) :
    (K/a^6)*(2*Real.pi*(a^(101/100:ℝ))^2)=(2*Real.pi*K)*a^(-199/50:ℝ) := by
  rw [←Real.rpow_mul_natCast ha.le]
  calc
    _=((2*Real.pi*K)*a^((101/100)*2:ℝ))/a^6 := by ring_nf
    _=_ := by rw [←Real.rpow_natCast a 6,div_rpow_monomial ha]; norm_num

lemma transfer_power_budget {a C D K : ℝ} (ha : 0<a) (ha1 : a≤1)
    (hC : 0≤C) (hD : 0≤D) (hK : 0≤K) :
    a^(-799/200:ℝ)+(5/(4*a^(101/100:ℝ)*a^(-799/200:ℝ)))*(2*a^(-349/50:ℝ))+
      C*a^(-21/5:ℝ)*(a^(101/100:ℝ)+2*a^(6/5:ℝ))^(1/5:ℝ)+
      C*a^(-21/5:ℝ)*(2*a^(6/5:ℝ))^(1/5:ℝ)+
      Real.sqrt (D*a^(-29/5:ℝ))/a+(K/a^6)*(2*Real.pi*(a^(101/100:ℝ))^2)≤
      (7/2+2*C*3^(1/5:ℝ)+Real.sqrt D+2*Real.pi*K)*a^(-1999/500:ℝ) := by
  obtain ⟨hbr,hra⟩ := transfer_radius_le ha ha1
  have hN₁ := transfer_near_power ha (by positivity : 0≤a^(101/100:ℝ)+2*a^(6/5:ℝ))
    (by linarith : a^(101/100:ℝ)+2*a^(6/5:ℝ)≤3*a^(101/100:ℝ)) C hC
  have hN₂ := transfer_near_power ha (by positivity : 0≤2*a^(6/5:ℝ))
    (by linarith [Real.rpow_nonneg ha.le (101/100:ℝ)] : 2*a^(6/5:ℝ)≤3*a^(101/100:ℝ)) C hC
  have h1 := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge ha ha1 (by norm_num : (-1999/500:ℝ)≤-799/200)) (by norm_num : (0:ℝ)≤7/2)
  have h2 := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge ha ha1 (by norm_num : (-1999/500:ℝ)≤-39/10)) (Real.sqrt_nonneg D)
  have h3 := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge ha ha1 (by norm_num : (-1999/500:ℝ)≤-199/50)) (by positivity : 0≤2*Real.pi*K)
  rw [transfer_gap_power ha,transfer_deleted_power ha hD,transfer_tfnear_power ha]
  nlinarith
end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma atomicTransferConstant_nonneg : 0≤atomicTransferConstant := by
  unfold atomicTransferConstant
  positivity [atomicNearConstant_nonneg,atomicPatchCountFactor_nonneg,atomicCountConstant_ge_two,
    tfInteriorConstant_nonneg thomasFermiKineticConstant,thomasFermiKineticConstant_pos]

theorem exists_atomic_fresh_field_transfer : ∃ s : ℝ, 0 < s ∧ s≤1 ∧
    ∀ {J n : ℕ} (S : Nuclei J) (hatom : ∀ i,S.position i=0)
    (u : H1Vector n), Antisymmetric u → mass u=1 →
    ∀ {E δ : ℝ}, (E:EReal)≤unrestrictedFormBottom S → form S u≤E+δ → 0≤δ →
    ∀ (y : Space) (hy : y≠0), atomicCellScale y < s → δ≤(atomicCellScale y)^(-349/50:ℝ) →
    ∃ t : ℝ, ∃ ht : t∈Set.Icc (5*atomicCellScale y) (6*atomicCellScale y),
    ∃ T : AtomicBudgetHistory S u (thinIMS u y t ((atomicCellScale y)^(6/5:ℝ))) 1,
      T.ensemble.totalForm S≤form S u+thinIMS u y t ((atomicCellScale y)^(6/5:ℝ)) ∧
      T.ensemble.OutFermionic ∧ T.ensemble.CoreSupported {z | t≤‖z-y‖} ∧
      T.ensemble.OutSupported (Metric.closedBall y (t+(atomicCellScale y)^(6/5:ℝ))) ∧
      atomicPatchTFGap S hatom T.ensemble y hy ((atomicCellScale y)^(6/5:ℝ))
        (Real.rpow_pos_of_pos (atomicCellScale_pos hy) _) t ht.2≤2*(atomicCellScale y)^(-349/50:ℝ) ∧
      T.ensemble.deletedSquare y t ((atomicCellScale y)^(6/5:ℝ))≤
        (72*atomicPatchCountFactor*atomicCountConstant)*(atomicCellScale y)^(-29/5:ℝ) ∧
      |coreScreenedField S u y-atomicPatchMeanField S hatom T.ensemble y hy
        ((atomicCellScale y)^(6/5:ℝ)) (Real.rpow_pos_of_pos (atomicCellScale_pos hy) _) t ht.2|≤
        atomicTransferConstant*(atomicCellScale y)^(-1999/500:ℝ) := by
  obtain ⟨s₀,hs₀,hs₀1,Hpatch⟩ := exists_atomic_small_gap_with_deleted
  obtain ⟨s₁,hs₁,hs₁1,Hnear⟩ := exists_atomic_near_scale
  obtain ⟨s₂,hs₂,hs₂1,Hscale⟩ := exists_atomic_refined_small_scale
  refine ⟨min s₀ (min s₁ s₂),lt_min hs₀ (lt_min hs₁ hs₂),
    (min_le_left _ _).trans hs₀1,?_⟩
  intro J n S hatom u hu hm E δ hE he hδ y hy hys hd
  let a := atomicCellScale y
  have ha : 0<a := atomicCellScale_pos hy
  have ha₀ : a < s₀ := hys.trans_le (min_le_left _ _)
  have ha₁ : a < s₁ := hys.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have ha₂ : a < s₂ := hys.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have ha1 : a≤1 := ha₀.le.trans hs₀1
  have hsmall := (Hscale a ha ha₂).1
  have hb : 0<a^(6/5:ℝ) := Real.rpow_pos_of_pos ha _
  have hr : 0<a^(101/100:ℝ) := Real.rpow_pos_of_pos ha _
  have hε : 0<a^(-799/200:ℝ) := Real.rpow_pos_of_pos ha _
  obtain ⟨hbr,hra⟩ := transfer_radius_le ha ha1
  obtain ⟨t,ht,T,hT,ho,hcs,hos,hgap,hdel⟩ := Hpatch S hatom u hu hm hE he hδ y hy ha₀ hd
  refine ⟨t,ht,T,hT,ho,hcs,hos,hgap,hdel,?_⟩
  have HF := fresh_patch_field_transfer S T.ensemble u T.law (T.mass_eq.trans hm)
    ha hb hsmall ht y (atomic_patch_nucleus_distance S hatom y) hr hra hε hcs
  change |coreScreenedField S u y-atomicPatchMeanField S hatom T.ensemble y hy
      (a^(6/5:ℝ)) hb t ht.2|≤
    a^(-799/200:ℝ)+(5/(4*a^(101/100:ℝ)*a^(-799/200:ℝ)))*
      atomicPatchTFGap S hatom T.ensemble y hy (a^(6/5:ℝ)) hb t ht.2+
    potentialForm (nearPotential y (a^(101/100:ℝ)+2*a^(6/5:ℝ))) u+
    potentialForm (nearPotential y (2*a^(6/5:ℝ))) u+Real.sqrt (T.ensemble.deletedSquare y t (a^(6/5:ℝ)))/a+
    ((tfInteriorConstant thomasFermiKineticConstant/(thomasFermiKineticConstant*(5/3:ℝ)))^(3/2:ℝ)/a^6)*
      (2*Real.pi*(a^(101/100:ℝ))^2) at HF
  have HN₁ := Hnear S hatom u hu hm hE he hδ y hy ha₁ hd
    (R := a^(101/100:ℝ)+2*a^(6/5:ℝ)) (by positivity) (by change _≤4*a; linarith)
  have HN₂ := Hnear S hatom u hu hm hE he hδ y hy ha₁ hd
    (R := 2*a^(6/5:ℝ)) (by positivity) (by change _≤4*a; linarith)
  have HG := mul_le_mul_of_nonneg_left hgap (show 0≤5/(4*a^(101/100:ℝ)*a^(-799/200:ℝ)) by positivity)
  have HD := div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hdel) ha.le
  have Hpower := transfer_power_budget ha ha1 atomicNearConstant_nonneg
    (show 0≤72*atomicPatchCountFactor*atomicCountConstant by positivity [atomicPatchCountFactor_nonneg,atomicCountConstant_ge_two])
    (show 0≤(tfInteriorConstant thomasFermiKineticConstant/(thomasFermiKineticConstant*(5/3:ℝ)))^(3/2:ℝ) by
      positivity [tfInteriorConstant_nonneg thomasFermiKineticConstant,thomasFermiKineticConstant_pos])
  change _≤atomicTransferConstant*a^(-1999/500:ℝ)
  unfold atomicTransferConstant
  dsimp only [a] at HF HN₁ HN₂ HG HD Hpower ⊢
  linarith
end Coulomb

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

theorem packet_potential_newton (g : 𝓢(Position,ℝ)) (hm : (∫ w,g w^2)=1)
    (hrad : ∀ w,g w=g (EuclideanSpace.single 0 ‖w‖))
    {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s)
    {z y : Position} (hyz : y≠z) :
    0≤potentialOf (packetKernel g c r₀ s z) y ∧
    potentialOf (packetKernel g c r₀ s z) y ≤ coulombKernel (y-z) := by
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
  rw [packet_potential_center_shift]
  refine ⟨integral_nonneg (fun w => mul_nonneg (Coulomb.coulombKernel_nonneg _) (hp w)),?_⟩
  have H := Coulomb.radial_coulomb_integral_le (fixed_scaled_window_integrable g hm ht)
    (by fun_prop) hp hb hfr (sub_ne_zero.mpr hyz)
  rw [fixed_scaled_window_mass g hm ht,mul_one] at H
  exact H

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

theorem packet_potential_near_deficit (g : 𝓢(Position,ℝ)) (hm : (∫ w,g w^2)=1)
    (hrad : ∀ w,g w=g (EuclideanSpace.single 0 ‖w‖))
    (hgs : ∀ w,1<‖w‖ → g w=0)
    {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s)
    (hq : c*(1+packetExponent)*s^packetExponent≤1/2)
    {z y : Position} (hyz : y≠z) :
    0 ≤ coulombKernel (y-z)-potentialOf (packetKernel g c r₀ s z) y ∧
    coulombKernel (y-z)-potentialOf (packetKernel g c r₀ s z) y≤
      (Metric.closedBall y (2*packetWidth c r₀ s y)).indicator
        (fun z => coulombKernel (y-z)) z := by
  have H := packet_potential_newton g hm hrad hc hr hs hyz
  refine ⟨sub_nonneg.mpr H.2,?_⟩
  by_cases hz : z∈Metric.closedBall y (2*packetWidth c r₀ s y)
  · rw [Set.indicator_of_mem hz]
    linarith [H.1]
  · rw [Set.indicator_of_notMem hz]
    have hd : 2*packetWidth c r₀ s y<‖z-y‖ := by
      simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using hz
    have hl := packetWidth_lipschitz hc.le hr hs z y
    have hi := mul_le_mul_of_nonneg_right hq (norm_nonneg (z-y))
    have hsep : packetWidth c r₀ s z≤‖y-z‖ := by
      rw [norm_sub_rev]
      have hle := (le_abs_self (packetWidth c r₀ s z-packetWidth c r₀ s y)).trans hl
      linarith
    rw [packet_potential_newton_eq g hm hrad hgs hc hr hs hsep,sub_self]
end NeutralAtom
end

end
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
attribute [-instance] _root_.OAI.NeutralAtom.observationSample_standardBorel
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

theorem rawPacketPotential_near_deficit {n : ℕ} (g : 𝓢(Position,ℝ)) (hm : (∫ w,g w^2)=1)
    (hrad : ∀ w,g w=g (EuclideanSpace.single 0 ‖w‖))
    (hgs : ∀ w,1<‖w‖ → g w=0)
    {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s)
    (hq : c*(1+packetExponent)*s^packetExponent≤1/2)
    (x : Configuration n) (y : Position) (hxy : ∀ i,x i≠y) :
    0≤(∑ i : Fin n,coulombKernel (y-x i))-potentialOf (rawPacketDensity g c r₀ s x) y ∧
    (∑ i : Fin n,coulombKernel (y-x i))-potentialOf (rawPacketDensity g c r₀ s x) y≤
      ∑ i : Fin n,(Metric.closedBall y (2*packetWidth c r₀ s y)).indicator
        (fun z => coulombKernel (y-z)) (x i) := by
  rw [rawPacketPotential_sum g hm hc hr hs,←Finset.sum_sub_distrib]
  refine ⟨Finset.sum_nonneg (fun i _ => ?_),Finset.sum_le_sum (fun i _ => ?_)⟩
  · exact (packet_potential_near_deficit g hm hrad hgs hc hr hs hq (hxy i).symm).1
  · exact (packet_potential_near_deficit g hm hrad hgs hc hr hs hq (hxy i).symm).2

lemma integrable_rawLaw_of_weight {n : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ,MemLp (ψ σ) 2 volume) (F : Configuration n → ℝ)
    (hi : Integrable (fun x => F x*configurationDensity ψ x)) :
    Integrable F (rawLaw ψ) := by
  have HH := (integrable_withDensity_iff_integrable_smul₀'
    (integrable_configurationDensity hψ).aemeasurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) (g := F))
  apply HH.mpr
  simpa only [ENNReal.toReal_ofReal (configurationDensity_nonneg ψ _),smul_eq_mul,mul_comm] using hi

lemma integrable_rawLaw_oneBody {n : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ,MemLp (ψ σ) 2 volume) (W : Position → ℝ)
    (hi : ∀ σ i,Integrable (fun x : Configuration n => W (x i)*‖ψ σ x‖^2)) :
    Integrable (fun x => ∑ i : Fin n,W (x i)) (rawLaw ψ) := by
  apply integrable_rawLaw_of_weight hψ
  simp only [Finset.sum_mul,configurationDensity,Finset.mul_sum]
  exact integrable_finsetSum _ (fun σ _ => integrable_finsetSum _ (fun i _ => hi σ i))

lemma fromH1_raw_potential_integral {n : ℕ} (u : Coulomb.H1Vector n) (y : Position) :
    (∫ x, (∑ i : Fin n,coulombKernel (y-x i)) ∂rawLaw (fromH1Wave u))=Coulomb.coreCoulombPotential u y := by
  have hψ (σ : Spins n) : MemLp (fromH1Wave u σ) 2 volume :=
    (u.value_L2 σ).comp_measurePreserving (flattenConfiguration_measurePreserving n)
  rw [integral_rawLaw hψ]
  unfold rawExpectation configurationDensity
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun σ _ => by
    simp only [Finset.sum_mul]
    exact integrable_finsetSum _ (fun i _ => fromH1_coulomb_weight_integrable u y σ i))]
  unfold Coulomb.coreCoulombPotential
  apply Finset.sum_congr rfl
  intro σ _
  rw [show (fun x : Configuration n => (∑ i,coulombKernel (y-x i))*‖fromH1Wave u σ x‖^2)=
    fun x => ∑ i : Fin n,coulombKernel (y-x i)*‖fromH1Wave u σ x‖^2 by funext x; rw [Finset.sum_mul]]
  rw [integral_finsetSum _ (fun i _ => fromH1_coulomb_weight_integrable u y σ i)]
  apply Finset.sum_congr rfl
  intro i _
  have H := (flattenConfiguration_measurePreserving n).integral_comp'
    (fun x => Coulomb.coulombKernel (Coulomb.position x i-y)*‖u.value σ x‖^2)
  change (∫ x : Configuration n,Coulomb.coulombKernel (x i-y)*‖fromH1Wave u σ x‖^2)=_ at H
  simpa only [coulombKernel,Coulomb.coulombKernel,norm_sub_rev] using H

theorem physical_master_near_deficit {N : ℕ} (u : Coulomb.H1Vector (N+1))
    (ha : Coulomb.Antisymmetric u) (hn : Coulomb.mass u=1)
    (g : 𝓢(Position,ℝ)) (hm : (∫ w,g w^2)=1)
    (hrad : ∀ w,g w=g (EuclideanSpace.single 0 ‖w‖))
    (hgs : ∀ w,1<‖w‖ → g w=0)
    {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s)
    (hq : c*(1+packetExponent)*s^packetExponent≤1/2) (y : Position) :
    0≤Coulomb.coreCoulombPotential u y-
      potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y ∧
    Coulomb.coreCoulombPotential u y-
      potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y≤
      ∫ z in Metric.closedBall y (2*packetWidth c r₀ s y),coulombKernel (y-z)*density (fromH1Wave u) z := by
  have hd := fromH1_domain u ha
  have hn' : normSquared (fromH1Wave u)=1 := (fromH1_mass u).trans hn
  have := rawLaw_isProbability hd.2.2.1 hn'
  have hgc : HasCompactSupport (g : Position → ℝ) :=
    HasCompactSupport.intro (isCompact_closedBall (0:Position) 1) (fun z hz =>
      hgs z (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz))
  have hraw := integrable_rawLaw_oneBody hd.2.2.1 (fun z => coulombKernel (y-z))
    (fromH1_coulomb_weight_integrable u y)
  have hnear := integrable_rawLaw_oneBody hd.2.2.1
    ((Metric.closedBall y (2*packetWidth c r₀ s y)).indicator (fun z => coulombKernel (y-z)))
    (fromH1_coulomb_near_weight_integrable u y _)
  have hms := integrable_rawPacketPotential g.continuous hgc hm hc hr hs (rawLaw (fromH1Wave u)) y
  have hpt : ∀ᵐ x ∂rawLaw (fromH1Wave u),
      0≤(∑ i : Fin (N+1),coulombKernel (y-x i))-potentialOf (rawPacketDensity g c r₀ s x) y ∧
      (∑ i : Fin (N+1),coulombKernel (y-x i))-potentialOf (rawPacketDensity g c r₀ s x) y≤
        ∑ i : Fin (N+1),(Metric.closedBall y (2*packetWidth c r₀ s y)).indicator
          (fun z => coulombKernel (y-z)) (x i) := by
    filter_upwards [rawLaw_no_fixed_particle hd.1 hd.2.2.1 hn' y] with x hx
    exact rawPacketPotential_near_deficit g hm hrad hgs hc hr hs hq x y hx
  have he : Coulomb.coreCoulombPotential u y-potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y=
      ∫ x,((∑ i : Fin (N+1),coulombKernel (y-x i))-potentialOf (rawPacketDensity g c r₀ s x) y) ∂rawLaw (fromH1Wave u) := by
    rw [integral_sub hraw hms,fromH1_raw_potential_integral,mixturePacketPotential g.continuous hgc hm hc hr hs]
  rw [he]
  refine ⟨integral_nonneg_of_ae (hpt.mono (fun _ hx => hx.1)),?_⟩
  calc
    _≤∫ x,(∑ i : Fin (N+1),(Metric.closedBall y (2*packetWidth c r₀ s y)).indicator
          (fun z => coulombKernel (y-z)) (x i)) ∂rawLaw (fromH1Wave u) :=
      integral_mono_ae (hraw.sub hms) hnear (hpt.mono (fun _ hx => hx.2))
    _=_ := by
      rw [integral_rawLaw hd.2.2.1,rawExpectation_oneBody_eq_density hd.1 _
        (fromH1_coulomb_near_weight_integrable u y _),←integral_indicator measurableSet_closedBall]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        by_cases hz : z∈Metric.closedBall y (2*packetWidth c r₀ s y) <;> simp [hz]
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
namespace NeutralAtom

lemma observationEventOffset_mono_probability {H : Type*} [Fintype H]
    (ℓ : H → ℝ) (D : ℝ) {p q : ℝ} (hp : 0<p) (hpq : p ≤ q) (hq : q ≤ 1) :
    D+observationEventEnergyConstant*observationWidthSquareSum ℓ*(1-Real.log q)^5  ≤
    D+observationEventEnergyConstant*observationWidthSquareSum ℓ*(1-Real.log p)^5 := by
  have hlog := Real.log_le_log hp hpq
  have hlog0 := Real.log_nonpos ((hp.trans_le hpq).le) hq
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by linarith) (by linarith) 5)
    (mul_nonneg observationEventEnergyConstant_pos.le (observationWidthSquareSum_nonneg ℓ)))

end NeutralAtom

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
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ObservationPatchScale
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

lemma inverseObservationOffset_scaled_tendsto (D : ℝ) :
    Tendsto (fun r => inverseObservationOffset D r*r^(349/50:ℝ)) (𝓝[>] 0) (𝓝 0) := by
  have ht := (tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<124/125)).sub
    ((tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0:ℝ)<124/125)).const_mul 42)
  have hh := ((tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<349/50)).const_mul D).add
    ((ht.pow 5).const_mul observationEventEnergyConstant)
  simp only [mul_zero,sub_self,zero_pow (by decide : 5≠0),add_zero] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr : 0 < r := hr
  have hpn : r^(101/100:ℝ)≠0 := (Real.rpow_pos_of_pos hr _).ne'
  have hmul : (r^(124/125:ℝ))^5*(r^(101/100:ℝ))^2=r^(349/50:ℝ) := by
    rw [←Real.rpow_natCast (r^(124/125:ℝ)) 5,←Real.rpow_mul hr.le,
      ←Real.rpow_natCast (r^(101/100:ℝ)) 2,←Real.rpow_mul hr.le,←Real.rpow_add hr]
    norm_num
  have hratio : ((r^(101/100:ℝ))⁻¹)^2*r^(349/50:ℝ)=(r^(124/125:ℝ))^5 := by
    rw [←hmul]
    field_simp
  dsimp [inverseObservationOffset]
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  calc
    D*r^(349/50:ℝ)+observationEventEnergyConstant*(r^(124/125:ℝ)-42*(Real.log r*r^(124/125:ℝ)))^5 =
      D*r^(349/50:ℝ)+observationEventEnergyConstant*(r^(124/125:ℝ))^5*(1-42*Real.log r)^5 := by ring
    _ = _ := by rw [←hratio]; ring

lemma inverseObservationOffset_nonneg {D r : ℝ} (hD : 0≤D) (hr : 0 < r) (hr1 : r≤1) :
    0 ≤ inverseObservationOffset D r := by
  have hl : Real.log (r^42)≤0 := Real.log_nonpos (by positivity) (pow_le_one₀ hr.le hr1)
  exact add_nonneg hD (mul_nonneg (mul_nonneg observationEventEnergyConstant_pos.le
    (sq_nonneg _)) (pow_nonneg (by linarith) _))

end NeutralAtom

end
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_RetainedInverseOffset
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

lemma retainedInverseOffset_scaled_tendsto (D : ℝ) :
    Tendsto (fun r => retainedInverseOffset D r*r^(349/50:ℝ)) (𝓝[>] 0) (𝓝 0) := by
  have H := ((tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<349/50)).const_mul D).add
    ((inverseObservationOffset_scaled_tendsto 0).const_mul (4/3:ℝ))
  simp only [mul_zero,add_zero] at H
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext r
  unfold retainedInverseOffset
  ring

lemma retainedInverseOffset_nonneg {D r : ℝ} (hD : 0≤D) (hr : 0 < r) (hr1 : r≤1) :
    0 ≤ retainedInverseOffset D r :=
  add_nonneg hD (mul_nonneg (by norm_num) (inverseObservationOffset_nonneg (by rfl) hr hr1))

lemma exists_retainedInverseOffset_small {D A : ℝ} (hD : 0≤D) (hA : 0<A) :
    ∃ s : ℝ, 0 < s ∧ s≤1 ∧ ∀ {r a : ℝ}, 0 < r → r < s → 0<a → a≤A*r →
      retainedInverseOffset D r≤a^(-349/50:ℝ) := by
  have ht := (retainedInverseOffset_scaled_tendsto D).mul_const (A^(349/50:ℝ))
  simp only [zero_mul] at ht
  have he : ∀ᶠ r : ℝ in 𝓝[>] 0,
      r<1 ∧ retainedInverseOffset D r*r^(349/50:ℝ)*A^(349/50:ℝ)<1 := by
    filter_upwards [(eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds,
      ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with r hr hh
    exact ⟨hr,hh⟩
  obtain ⟨s,hs,hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  refine ⟨min s 1,lt_min hs (by norm_num),min_le_right _ _,?_⟩
  intro r a hr hrs ha haA
  obtain ⟨hr1,hh⟩ := hsub ⟨hr,hrs.trans_le (min_le_left _ _)⟩
  have hδ := retainedInverseOffset_nonneg hD hr hr1.le
  have hm : retainedInverseOffset D r*a^(349/50:ℝ)≤1 := by
    calc
      _ ≤ retainedInverseOffset D r*(A*r)^(349/50:ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha.le haA (by norm_num)) hδ
      _ = retainedInverseOffset D r*r^(349/50:ℝ)*A^(349/50:ℝ) := by
        rw [Real.mul_rpow hA.le hr.le]; ring
      _ ≤ 1 := hh.le
  rw [neg_div,Real.rpow_neg ha.le,inv_eq_one_div]
  exact (le_div_iff₀ (Real.rpow_pos_of_pos ha _)).mpr hm

lemma retained_event_offset_le {r₀ D p : ℝ} (hr₀ : 0 < r₀) (J j : ℕ)
    (hp : (r₀*2^j)^42≤p) (hp1 : p≤1) :
    D+observationEventEnergyConstant*
      observationWidthSquareSum (fun k : RetainedScales J j => (r₀*2^k.val.val)^(101/100:ℝ))*
      (1-Real.log p)^5 ≤ retainedInverseOffset D (r₀*2^j) := by
  have hr : 0 < r₀*2^j := by positivity
  have hp0 : 0<p := (pow_pos hr _).trans_le hp
  have hm := observationEventOffset_mono_probability
    (fun k : RetainedScales J j => (r₀*2^k.val.val)^(101/100:ℝ)) D
    (pow_pos hr 42) hp hp1
  have hl : Real.log ((r₀*2^j)^42)≤0 :=
    Real.log_nonpos (pow_pos hr 42).le (hp.trans hp1)
  have hw := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (observationWidthSquareSum_retained_dyadic hr₀ J j)
      observationEventEnergyConstant_pos.le)
    (pow_nonneg (by linarith : 0≤1-Real.log ((r₀*2^j)^42)) 5)
  unfold retainedInverseOffset inverseObservationOffset
  linarith

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RadialBounds_AtomicMasterError
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

lemma physical_closed_near_le_open {N : ℕ} (u : Coulomb.H1Vector (N+1))
    (hu : Coulomb.Antisymmetric u) (y : Position) {R : ℝ} (hR : 0<R) :
    (∫ z in Metric.closedBall y R,coulombKernel (y-z)*density (fromH1Wave u) z)≤
      Coulomb.potentialForm (Coulomb.nearPotential y (2*R)) u := by
  rw [Coulomb.nearPotential_physical u hu]
  have hi := density_weight_integrable (fromH1Wave u) (fun z => coulombKernel (y-z))
    (fun σ => fromH1_coulomb_weight_integrable u y σ 0)
  have hh := setIntegral_mono_set (s := Metric.closedBall y R) (t := Metric.ball y (2*R)) hi.integrableOn
    (Eventually.of_forall (fun z => mul_nonneg (Coulomb.coulombKernel_nonneg _) (by unfold density; positivity)))
    (Eventually.of_forall (fun z (hz : z∈Metric.closedBall y R) =>
      (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hz).trans_lt (by linarith : R<2*R)))))
  simpa only [coulombKernel,Coulomb.coulombKernel,mul_comm] using hh

theorem exists_atomic_master_error_scale : ∃ s₀ : ℝ, 0 < s₀ ∧ s₀≤1 ∧
    ∀ {J N : ℕ} (S : Coulomb.Nuclei J), (∀ i,S.position i=0) →
    ∀ (u : Coulomb.H1Vector (N+1)), Coulomb.Antisymmetric u → Coulomb.mass u=1 →
    ∀ {E δ : ℝ}, (E:EReal)≤Coulomb.unrestrictedFormBottom S → Coulomb.form S u≤E+δ → 0≤δ →
    ∀ (y : Position), y≠0 → Coulomb.atomicCellScale y < s₀ → δ≤(Coulomb.atomicCellScale y)^(-349/50:ℝ) →
    ∀ (g : 𝓢(Position,ℝ)), (∫ w,g w^2)=1 →
    (∀ w,g w=g (EuclideanSpace.single 0 ‖w‖)) → (∀ w,1<‖w‖ → g w=0) →
    ∀ {c r₀ s : ℝ}, 0 < c → 0 < r₀ → 0 < s → c*(1+packetExponent)*s^packetExponent≤1/2 →
    packetWidth c r₀ s y≤Coulomb.atomicCellScale y →
    0≤Coulomb.coreCoulombPotential u y-
      potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y ∧
    Coulomb.coreCoulombPotential u y-
      potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y≤
      Coulomb.atomicNearConstant*(Coulomb.atomicCellScale y)^(-21/5:ℝ)*(4*packetWidth c r₀ s y)^(1/5:ℝ) := by
  obtain ⟨s₀,hs₀,hs₀1,H⟩ := Coulomb.exists_atomic_near_scale
  refine ⟨s₀,hs₀,hs₀1,?_⟩
  intro J N S hatom u hu hm E δ hE hstate hδ y hy hys hd g hgm hrad hgs c r₀ s hc hr hs hq hw
  obtain ⟨hl,hh⟩ := physical_master_near_deficit u hu hm g hgm hrad hgs hc hr hs hq y
  have hp := packetWidth_pos hc hr hs y
  refine ⟨hl,hh.trans ?_⟩
  have hb := physical_closed_near_le_open u hu y (mul_pos (by norm_num : (0:ℝ)<2) hp)
  have hn := H S hatom u hu hm hE hstate hδ y hy hys hd
    (R := 4*packetWidth c r₀ s y) (by positivity) (by linarith)
  rw [show (2:ℝ)*(2*packetWidth c r₀ s y)=4*packetWidth c r₀ s y by ring] at hb
  exact hb.trans hn
end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_AtomicMasterRelative
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

lemma master_relative_deficit {a w θ : ℝ} (ha : 0<a) (hθ : 0≤θ) (hw : 0≤w)
    (hwidth : w≤θ*a) :
    Coulomb.atomicNearConstant*a^(-21/5:ℝ)*(4*w)^(1/5:ℝ)≤
      Coulomb.atomicNearConstant*(4*θ)^(1/5:ℝ)*a^(-4:ℝ) := by
  calc
    _≤Coulomb.atomicNearConstant*a^(-21/5:ℝ)*((4*θ)*a)^(1/5:ℝ) := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.rpow_le_rpow (by positivity) (by nlinarith) (by norm_num)
      · positivity [Coulomb.atomicNearConstant_nonneg]
    _=_ := by
      rw [Real.mul_rpow (by positivity : 0≤4*θ) ha.le]
      calc
        _=Coulomb.atomicNearConstant*(4*θ)^(1/5:ℝ)*(a^(-21/5:ℝ)*a^(1/5:ℝ)) := by ring
        _=_ := by rw [←Real.rpow_add ha]; norm_num

theorem exists_atomic_master_fresh_relative_transfer : ∃ s₀ : ℝ, 0 < s₀ ∧ s₀≤1 ∧
    ∀ {J N : ℕ} (S : Coulomb.Nuclei J) (hatom : ∀ i,S.position i=0)
    (u : Coulomb.H1Vector (N+1)), Coulomb.Antisymmetric u → Coulomb.mass u=1 →
    ∀ {E δ : ℝ}, (E:EReal)≤Coulomb.unrestrictedFormBottom S → Coulomb.form S u≤E+δ → 0≤δ →
    ∀ (y : Position) (hy : y≠0), Coulomb.atomicCellScale y < s₀ → δ≤(Coulomb.atomicCellScale y)^(-349/50:ℝ) →
    ∃ t : ℝ, ∃ ht : t∈Set.Icc (5*Coulomb.atomicCellScale y) (6*Coulomb.atomicCellScale y),
    ∃ T : Coulomb.AtomicBudgetHistory S u (Coulomb.thinIMS u y t ((Coulomb.atomicCellScale y)^(6/5:ℝ))) 1,
      T.ensemble.totalForm S≤Coulomb.form S u+Coulomb.thinIMS u y t ((Coulomb.atomicCellScale y)^(6/5:ℝ)) ∧
      T.ensemble.OutFermionic ∧ T.ensemble.CoreSupported {z | t≤‖z-y‖} ∧
      T.ensemble.OutSupported (Metric.closedBall y (t+(Coulomb.atomicCellScale y)^(6/5:ℝ))) ∧
      Coulomb.atomicPatchTFGap S hatom T.ensemble y hy ((Coulomb.atomicCellScale y)^(6/5:ℝ))
        (Real.rpow_pos_of_pos (Coulomb.atomicCellScale_pos hy) _) t ht.2≤2*(Coulomb.atomicCellScale y)^(-349/50:ℝ) ∧
      T.ensemble.deletedSquare y t ((Coulomb.atomicCellScale y)^(6/5:ℝ))≤
        (72*Coulomb.atomicPatchCountFactor*Coulomb.atomicCountConstant)*(Coulomb.atomicCellScale y)^(-29/5:ℝ) ∧
      ∀ (g : 𝓢(Position,ℝ)), (∫ w,g w^2)=1 →
      (∀ w,g w=g (EuclideanSpace.single 0 ‖w‖)) → (∀ w,1<‖w‖ → g w=0) →
      ∀ {c r₀ s θ : ℝ}, 0 < c → 0 < r₀ → 0 < s → c*(1+packetExponent)*s^packetExponent≤1/2 →
      0≤θ → θ≤1 → packetWidth c r₀ s y≤θ*Coulomb.atomicCellScale y →
      |(Coulomb.attraction S y-potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y)-
        Coulomb.atomicPatchMeanField S hatom T.ensemble y hy ((Coulomb.atomicCellScale y)^(6/5:ℝ))
          (Real.rpow_pos_of_pos (Coulomb.atomicCellScale_pos hy) _) t ht.2|≤
        (Coulomb.atomicTransferConstant*(Coulomb.atomicCellScale y)^(1/500:ℝ)+
          Coulomb.atomicNearConstant*(4*θ)^(1/5:ℝ))*(Coulomb.atomicCellScale y)^(-4:ℝ) := by
  obtain ⟨s₀,hs₀,hs₀1,Hfresh⟩ := Coulomb.exists_atomic_fresh_field_transfer
  obtain ⟨s₁,hs₁,hs₁1,Hmaster⟩ := exists_atomic_master_error_scale
  refine ⟨min s₀ s₁,lt_min hs₀ hs₁,(min_le_left _ _).trans hs₀1,?_⟩
  intro J N S hatom u hu hm E δ hE he hδ y hy hys hd
  have ha := Coulomb.atomicCellScale_pos hy
  have hay₀ := hys.trans_le (min_le_left _ _)
  have hay₁ := hys.trans_le (min_le_right _ _)
  obtain ⟨t,ht,T,hT,ho,hcs,hos,hG,hD,hF⟩ := Hfresh S hatom u hu hm hE he hδ y hy hay₀ hd
  refine ⟨t,ht,T,hT,ho,hcs,hos,hG,hD,?_⟩
  intro g hgm hrad hgs c r₀ s θ hc hr hs hq hθ hθ1 hw
  have ha1 : Coulomb.atomicCellScale y≤1 := hay₀.le.trans hs₀1
  have hwa : packetWidth c r₀ s y≤Coulomb.atomicCellScale y := hw.trans (by nlinarith)
  have HM := Hmaster S hatom u hu hm hE he hδ y hy hay₁ hd g hgm hrad hgs hc hr hs hq hwa
  have HB := HM.2.trans (master_relative_deficit ha hθ (packetWidth_pos hc hr hs y).le hw)
  have HT := abs_sub_le (Coulomb.attraction S y-potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y)
    (Coulomb.coreScreenedField S u y) (Coulomb.atomicPatchMeanField S hatom T.ensemble y hy
      ((Coulomb.atomicCellScale y)^(6/5:ℝ)) (Real.rpow_pos_of_pos ha _) t ht.2)
  have hEq : (Coulomb.attraction S y-potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y)-
      Coulomb.coreScreenedField S u y=Coulomb.coreCoulombPotential u y-
        potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y := by unfold Coulomb.coreScreenedField; ring
  rw [hEq,abs_of_nonneg HM.1] at HT
  have hp : (Coulomb.atomicCellScale y)^(-1999/500:ℝ)=
      (Coulomb.atomicCellScale y)^(1/500:ℝ)*(Coulomb.atomicCellScale y)^(-4:ℝ) := by
    rw [←Real.rpow_add ha]
    norm_num
  rw [hp] at hF
  nlinarith
end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_AtomicMasterUniform
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

lemma exists_atomic_master_uniform_error {c A ε : ℝ} (hc : 0 < c) (hA : 0<A)
    (hε : 0<ε) : ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ {s : ℝ}, 0 < s → s < s₀ →
      c*(1+packetExponent)*s^packetExponent≤1/2 ∧
      100000*c*s^packetExponent≤1 ∧
      ∀ {a : ℝ}, 0<a → a≤A*s →
      Coulomb.atomicTransferConstant*a^(1/500:ℝ)+
        Coulomb.atomicNearConstant*(4*(100000*c*s^packetExponent))^(1/5:ℝ)≤ε := by
  have hw : 0<packetExponent := by norm_num [packetExponent]
  have ht := (tendsto_positive_rpow_zero hw).const_mul (c*(1+packetExponent))
  have hu := (tendsto_positive_rpow_zero hw).const_mul (100000*c)
  have he := ((tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<1/500)).const_mul
    (Coulomb.atomicTransferConstant*A^(1/500:ℝ))).add
    ((tendsto_positive_rpow_zero (div_pos hw (by norm_num : (0:ℝ)<5))).const_mul
      (Coulomb.atomicNearConstant*(400000*c)^(1/5:ℝ)))
  simp only [mul_zero,add_zero] at ht hu he
  have HH : ∀ᶠ s : ℝ in 𝓝[>] 0,
      c*(1+packetExponent)*s^packetExponent<1/2 ∧
      100000*c*s^packetExponent<1 ∧
      Coulomb.atomicTransferConstant*A^(1/500:ℝ)*s^(1/500:ℝ)+
        Coulomb.atomicNearConstant*(400000*c)^(1/5:ℝ)*s^(packetExponent/5)<ε := by
    filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)),
      hu.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),he.eventually (gt_mem_nhds hε)] with s hs₁ hs₂ hs₃
    exact ⟨hs₁,hs₂,hs₃⟩
  obtain ⟨s₀,hs₀,Hs₀⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp HH
  refine ⟨s₀,hs₀,?_⟩
  intro s hs hss
  obtain ⟨hq,hθ,herr⟩ := Hs₀ ⟨hs,hss⟩
  refine ⟨hq.le,hθ.le,?_⟩
  intro a ha hsa
  have hca : 0≤Coulomb.atomicTransferConstant := Coulomb.atomicTransferConstant_nonneg
  have hfirst := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow ha.le hsa (by norm_num : (0:ℝ)≤1/500)) hca
  have hpow : (4*(100000*c*s^packetExponent))^(1/5:ℝ)=
      (400000*c)^(1/5:ℝ)*s^(packetExponent/5) := by
    rw [show 4*(100000*c*s^packetExponent)=(400000*c)*s^packetExponent by ring,
      Real.mul_rpow (by positivity : 0≤400000*c) (Real.rpow_nonneg hs.le _),
      ←Real.rpow_mul hs.le]
    congr 2
    ring
  rw [Real.mul_rpow hA.le hs.le] at hfirst
  rw [hpow]
  nlinarith

theorem exists_atomic_master_fresh_uniform_transfer {c A ε : ℝ}
    (hc : 0 < c) (hA : 0<A) (hε : 0<ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ {J N : ℕ} (S : Coulomb.Nuclei J)
    (hatom : ∀ i,S.position i=0) (u : Coulomb.H1Vector (N+1)),
    Coulomb.Antisymmetric u → Coulomb.mass u=1 →
    ∀ {E δ : ℝ}, (E:EReal)≤Coulomb.unrestrictedFormBottom S → Coulomb.form S u≤E+δ → 0≤δ →
    ∀ {r₀ s : ℝ}, 0 < r₀ → 0 < s → s < s₀ →
    ∀ (y : Position) (hy : y≠0), r₀≤‖y‖ → Coulomb.atomicCellScale y≤A*s →
    δ≤(Coulomb.atomicCellScale y)^(-349/50:ℝ) →
    ∃ t : ℝ, ∃ ht : t∈Set.Icc (5*Coulomb.atomicCellScale y) (6*Coulomb.atomicCellScale y),
    ∃ T : Coulomb.AtomicBudgetHistory S u (Coulomb.thinIMS u y t ((Coulomb.atomicCellScale y)^(6/5:ℝ))) 1,
      T.ensemble.totalForm S≤Coulomb.form S u+Coulomb.thinIMS u y t ((Coulomb.atomicCellScale y)^(6/5:ℝ)) ∧
      T.ensemble.OutFermionic ∧ T.ensemble.CoreSupported {z | t≤‖z-y‖} ∧
      T.ensemble.OutSupported (Metric.closedBall y (t+(Coulomb.atomicCellScale y)^(6/5:ℝ))) ∧
      Coulomb.atomicPatchTFGap S hatom T.ensemble y hy ((Coulomb.atomicCellScale y)^(6/5:ℝ))
        (Real.rpow_pos_of_pos (Coulomb.atomicCellScale_pos hy) _) t ht.2≤2*(Coulomb.atomicCellScale y)^(-349/50:ℝ) ∧
      T.ensemble.deletedSquare y t ((Coulomb.atomicCellScale y)^(6/5:ℝ))≤
        (72*Coulomb.atomicPatchCountFactor*Coulomb.atomicCountConstant)*(Coulomb.atomicCellScale y)^(-29/5:ℝ) ∧
      ∀ (g : 𝓢(Position,ℝ)), (∫ w,g w^2)=1 →
      (∀ w,g w=g (EuclideanSpace.single 0 ‖w‖)) → (∀ w,1<‖w‖ → g w=0) →
      |(Coulomb.attraction S y-potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y)-
        Coulomb.atomicPatchMeanField S hatom T.ensemble y hy ((Coulomb.atomicCellScale y)^(6/5:ℝ))
          (Real.rpow_pos_of_pos (Coulomb.atomicCellScale_pos hy) _) t ht.2|≤
        ε*(Coulomb.atomicCellScale y)^(-4:ℝ) := by
  obtain ⟨s₁,hs₁,_,H⟩ := exists_atomic_master_fresh_relative_transfer
  obtain ⟨s₂,hs₂,Herr⟩ := exists_atomic_master_uniform_error hc hA hε
  refine ⟨min s₂ (s₁/A),lt_min hs₂ (div_pos hs₁ hA),?_⟩
  intro J N S hatom u hu hm E δ hE he hδ r₀ s hr hs hss y hy hry hya hd
  have has : Coulomb.atomicCellScale y < s₁ := hya.trans_lt (by
    have h := (lt_div_iff₀ hA).mp (hss.trans_le (min_le_right _ _))
    simpa only [mul_comm] using h)
  obtain ⟨hq,hθ,herr⟩ := Herr hs (hss.trans_le (min_le_left _ _))
  obtain ⟨t,ht,T,hTf,ho,hcs,hos,hG,hD,hF⟩ := H S hatom u hu hm hE he hδ y hy has hd
  refine ⟨t,ht,T,hTf,ho,hcs,hos,hG,hD,?_⟩
  intro g hgm hrad hgs
  have hwidth : packetWidth c r₀ s y≤(100000*c*s^packetExponent)*Coulomb.atomicCellScale y := by
    have hw := packetWidth_le c r₀ s hc.le hr hs y
    rw [max_eq_left hry,←Coulomb.atomicCellScale_norm y] at hw
    nlinarith
  have HF := hF g hgm hrad hgs hc hr hs hq (by positivity) hθ hwidth
  exact HF.trans (mul_le_mul_of_nonneg_right (herr (Coulomb.atomicCellScale_pos hy) hya)
    (Real.rpow_nonneg (Coulomb.atomicCellScale_nonneg y) _))
end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_RetainedMasterTransfer
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

theorem physical_retained_master_fresh_transfer_oai {D c A ε : ℝ}
    (hD : 0≤D) (hc : 0 < c) (hA : 0<A) (hε : 0<ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀≤1 ∧ ∀ {N J : ℕ} (Z : ℕ) (hZ : 1≤Z)
    {ψ : Wavefunction (N+1)} {g : Gradient (N+1)}, FormDomain ψ g → normSquared ψ=1 →
    (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)), FormDomain χ h → normSquared χ=1 →
      energy Z ψ g≤energy Z χ h) →
    ∀ {E : ℝ}, (E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g≤E+D → ∀ {r₀ s : ℝ}, 0 < r₀ → 0 < s → s < s₀ →
    ∀ (j : ℕ), r₀ * (2 : ℝ) ^ j ≤ s →
    ∀ {B : Set (Fin J → UnorderedArray (N+1))}, MeasurableSet B →
    (r₀*2^j)^42≤(observationLaw J (rawLaw ψ)).real
      (tailObservation (fun k : Fin J => r₀*2^k.val) j ⁻¹' B) →
    ∀ (y : Position) (hy : y≠0), r₀≤‖y‖ → Coulomb.atomicCellScale y≤A*(r₀*2^j) →
    ∃ u : Coulomb.H1Vector (N+1), Coulomb.Antisymmetric u ∧ Coulomb.mass u=1 ∧
      Coulomb.form (Coulomb.atom Z hZ) u≤E+retainedInverseOffset D (r₀*2^j) ∧
      (∀ F : Coulomb.Configuration (N+1) → ℝ, Coulomb.potentialForm F u=
        (stateWeightedIntegral ψ (arrayEventLikelihood
          (fun k : RetainedScales J j => (r₀*2^k.val.val)^(101/100:ℝ))
          (retainedTailObservation j ⁻¹' B)))⁻¹*
        stateWeightedIntegral ψ (fun x => arrayEventLikelihood
          (fun k : RetainedScales J j => (r₀*2^k.val.val)^(101/100:ℝ))
          (retainedTailObservation j ⁻¹' B) x*F (flattenConfiguration (N+1) x))) ∧
    ∃ t : ℝ, ∃ ht : t∈Set.Icc (5*Coulomb.atomicCellScale y) (6*Coulomb.atomicCellScale y),
    ∃ T : Coulomb.AtomicBudgetHistory (Coulomb.atom Z hZ) u
      (Coulomb.thinIMS u y t ((Coulomb.atomicCellScale y)^(6/5:ℝ))) 1,
      T.ensemble.totalForm (Coulomb.atom Z hZ)≤Coulomb.form (Coulomb.atom Z hZ) u+
        Coulomb.thinIMS u y t ((Coulomb.atomicCellScale y)^(6/5:ℝ)) ∧
      T.ensemble.OutFermionic ∧ T.ensemble.CoreSupported {z | t≤‖z-y‖} ∧
      T.ensemble.OutSupported (Metric.closedBall y (t+(Coulomb.atomicCellScale y)^(6/5:ℝ))) ∧
      Coulomb.atomicPatchTFGap (Coulomb.atom Z hZ) (by intro i; rfl) T.ensemble y hy
        ((Coulomb.atomicCellScale y)^(6/5:ℝ))
        (Real.rpow_pos_of_pos (Coulomb.atomicCellScale_pos hy) _) t ht.2≤
        2*(Coulomb.atomicCellScale y)^(-349/50:ℝ) ∧
      T.ensemble.deletedSquare y t ((Coulomb.atomicCellScale y)^(6/5:ℝ))≤
        (72*Coulomb.atomicPatchCountFactor*Coulomb.atomicCountConstant)*
          (Coulomb.atomicCellScale y)^(-29/5:ℝ) ∧
      ∀ (g₀ : 𝓢(Position,ℝ)), (∫ w,g₀ w^2)=1 →
      (∀ w,g₀ w=g₀ (EuclideanSpace.single 0 ‖w‖)) → (∀ w,1<‖w‖ → g₀ w=0) →
      |((Z:ℝ)*coulombKernel y-
          potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g₀ c r₀ s) y)-
        Coulomb.atomicPatchMeanField (Coulomb.atom Z hZ) (by intro i; rfl) T.ensemble y hy
          ((Coulomb.atomicCellScale y)^(6/5:ℝ))
          (Real.rpow_pos_of_pos (Coulomb.atomicCellScale_pos hy) _) t ht.2|≤
        ε*(Coulomb.atomicCellScale y)^(-4:ℝ) := by
  obtain ⟨s₁,hs₁,hs₁1,Hoff⟩ := exists_retainedInverseOffset_small hD hA
  obtain ⟨s₂,hs₂,Hpatch⟩ := exists_atomic_master_fresh_uniform_transfer hc hA hε
  refine ⟨min s₁ s₂,lt_min hs₁ hs₂,(min_le_left _ _).trans hs₁1,?_⟩
  intro N J Z hZ ψ g hd hn hmin E hE hbase r₀ s hr₀ hs hss j hrs B hB hprob y hy hry hya
  have hr : 0 < r₀*2^j := by positivity
  have hrs₁ : r₀*2^j < s₁ := hrs.trans_lt (hss.trans_le (min_le_left _ _))
  have := rawLaw_isProbability hd.2.2.1 hn
  have hp1 : (observationLaw J (rawLaw ψ)).real
      (tailObservation (fun k : Fin J => r₀*2^k.val) j ⁻¹' B)≤1 := measureReal_le_one
  have hpEq := physical_retainedTailEvent_probability hd.2.2.1 hn
    (fun k : Fin J => r₀*2^k.val) (fun k => by positivity) j hB
  have hp0 := (pow_pos hr 42).trans_le hprob
  obtain ⟨u,hu,hum,hue,hlaw⟩ := atomic_arrayEvent_state Z hZ hd hn hmin hbase
    (fun k : RetainedScales J j => (r₀*2^k.val.val)^(101/100:ℝ))
    (fun k => Real.rpow_pos_of_pos (by positivity) _)
    (hB.preimage (measurable_retainedTailObservation j))
    (fun p z => by simp only [mem_preimage,retainedTailObservation_permute])
    (hpEq ▸ hp0)
  have hδ := retainedInverseOffset_nonneg hD hr (hrs₁.le.trans hs₁1)
  have hue' : Coulomb.form (Coulomb.atom Z hZ) u≤E+retainedInverseOffset D (r₀*2^j) := by
    apply hue.trans
    apply add_le_add le_rfl
    apply retained_event_offset_le hr₀ J j
    · simpa only [←hpEq] using hprob
    · simpa only [←hpEq] using hp1
  refine ⟨u,hu,hum,hue',hlaw,?_⟩
  obtain ⟨t,ht,T,hT,ho,hcs,hos,hG,hdel,hF⟩ := Hpatch (Coulomb.atom Z hZ)
    (by intro i; rfl) u hu hum hE hue' hδ hr₀ hs (hss.trans_le (min_le_right _ _)) y hy hry
    (hya.trans (mul_le_mul_of_nonneg_left hrs hA.le))
    (Hoff hr hrs₁ (Coulomb.atomicCellScale_pos hy) hya)
  refine ⟨t,ht,T,hT,ho,hcs,hos,hG,hdel,?_⟩
  intro g₀ hgm hrad hgs
  have H := hF g₀ hgm hrad hgs
  simpa only [Coulomb.attraction,Coulomb.atom,Fin.sum_univ_one,zero_sub,sub_zero,norm_neg,
    Coulomb.coulombKernel,coulombKernel] using H
end NeutralAtom
end

end

end OAI
end

theorem solution : type_of% @OAI.NeutralAtom.physical_retained_master_fresh_transfer_oai := @OAI.NeutralAtom.physical_retained_master_fresh_transfer_oai
