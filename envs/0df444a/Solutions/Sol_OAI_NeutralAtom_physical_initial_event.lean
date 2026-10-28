-- Prove2me | solution 1 for OAI.NeutralAtom.physical_initial_event
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:24:03.385057+00:00
-- url     : https://prove2.me/submissions/d0ee1c9a-4842-4106-9e59-833443de31aa

import Mathlib
import Definitions.Def_CoulombRadii
import Definitions.Def_OAIQ062C007
import Theorems.Thm_OAI_NeutralAtom_atomic_global_master_potential

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
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
namespace Coulomb

lemma volume_closedBall_three (y : Space) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (Metric.closedBall y r) = 4*Real.pi/3*r^3 := by
  rw [Measure.addHaar_real_closedBall_eq_addHaar_real_ball,
    Measure.addHaar_real_ball_center,volume_real_ball_three r hr]

end Coulomb

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

end NeutralAtom
end
end
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

open MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace NeutralAtom

theorem continuous_packetWidth (c₁ r₀ s : ℝ) : Continuous (packetWidth c₁ r₀ s) := by
  unfold packetWidth
  fun_prop (disch := norm_num [packetExponent])

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

theorem mixturePacketDensity_mass {n : ℕ} {g : Position → ℝ} (hg : Continuous g)
    (hgnorm : (∫ y, g y^2)=1) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    (ν : Measure (Configuration n)) [IsProbabilityMeasure ν] :
    (∫ y, mixturePacketDensity ν g c₁ r₀ s y) = n := by
  unfold mixturePacketDensity
  have hi : Integrable (Function.uncurry (fun y x => rawPacketDensity g c₁ r₀ s x y))
      (volume.prod ν) := (rawPacketDensity_prod_integrable hg hgnorm hc hr hs ν).swap
  rw [integral_integral_swap hi]
  simp only [rawPacketDensity_mass g hgnorm hc hr hs, integral_const, probReal_univ,
    one_smul]

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
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_PhysicalBridge
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
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
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_NormalizedInversePoint
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

lemma separated_mesh_volume_bound (t : Finset Position) {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) (hball : ∀ x∈t,‖x‖ ≤ R)
    (hsep : ∀ x∈t,∀ y∈t,x≠y → ε < ‖x-y‖) :
    (t.card:ℝ)*(ε/3)^3 ≤ (R+ε/3)^3 := by
  have hdis : Set.PairwiseDisjoint (t:Set Position) (fun x => Metric.closedBall x (ε/3)) := by
    intro x hx y hy hxy
    apply Metric.closedBall_disjoint_closedBall
    rw [dist_eq_norm]
    linarith [hsep x hx y hy hxy]
  have hsub : (⋃ x∈t,Metric.closedBall x (ε/3)) ⊆ Metric.closedBall (0:Position) (R+ε/3) := by
    apply iUnion₂_subset
    intro x hx y hy
    rw [Metric.mem_closedBall,dist_zero_right]
    have hh : ‖y-x‖ ≤ ε/3 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hy
    have ht := norm_le_norm_add_norm_sub x y
    rw [norm_sub_rev x y] at ht
    linarith [hball x hx]
  have H := measureReal_mono (μ:=volume) hsub (isCompact_closedBall (0:Position) (R+ε/3)).measure_ne_top
  rw [measureReal_biUnion_finset hdis (fun _ _ => measurableSet_closedBall)
    (fun x _ => (isCompact_closedBall x (ε/3)).measure_ne_top),
    Coulomb.volume_closedBall_three _ (by positivity : 0 ≤ R+ε/3)] at H
  simp_rw [Coulomb.volume_closedBall_three _ (by positivity : 0 ≤ ε/3)] at H
  simp only [Finset.sum_const,nsmul_eq_mul] at H
  have he : (t.card:ℝ)*(4*Real.pi/3*(ε/3)^3)=(4*Real.pi/3)*((t.card:ℝ)*(ε/3)^3) := by ring
  rw [he] at H
  exact (mul_le_mul_iff_right₀ (by positivity : 0 < 4*Real.pi/3)).mp H

theorem exists_quantitative_mesh (S : Set Position) {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) (hball : ∀ x∈S,‖x‖ ≤ R) :
    ∃ t : Finset Position,(↑t:Set Position) ⊆ S ∧
      (∀ y∈S,∃ x∈t,‖y-x‖ ≤ ε) ∧
      (t.card:ℝ)*(ε/3)^3 ≤ (R+ε/3)^3 := by
  let P := fun t : Finset Position => (↑t:Set Position) ⊆ S ∧
    (∀ x∈t,∀ y∈t,x≠y → ε < ‖x-y‖)
  let A := {k : ℕ | ∃ t : Finset Position,t.card=k ∧ P t}
  have hb (k : ℕ) (hk : k∈A) : k ≤ ⌈(R+ε/3)^3/(ε/3)^3⌉₊ := by
    obtain ⟨t,rfl,ht⟩ := hk
    have H := separated_mesh_volume_bound t hR hε (fun x hx => hball x (ht.1 hx)) ht.2
    have hh : (t.card:ℝ) ≤ (R+ε/3)^3/(ε/3)^3 := (le_div_iff₀ (by positivity)).mpr H
    exact_mod_cast hh.trans (Nat.le_ceil _)
  have hAf : A.Finite := (Set.finite_Iic ⌈(R+ε/3)^3/(ε/3)^3⌉₊).subset hb
  have hAn : A.Nonempty := ⟨0,∅,by simp,by simp [P]⟩
  obtain ⟨k,hkf,hmaxf⟩ := hAf.toFinset.exists_max_image (fun k : ℕ => k)
    (by simpa only [Set.Finite.toFinset_nonempty] using hAn)
  have hk : k∈A := hAf.mem_toFinset.mp hkf
  have hmax (l : ℕ) (hl : l∈A) : l ≤ k := hmaxf l (hAf.mem_toFinset.mpr hl)
  obtain ⟨t,htk,ht⟩ := hk
  refine ⟨t,ht.1,?_,separated_mesh_volume_bound t hR hε (fun x hx => hball x (ht.1 hx)) ht.2⟩
  intro y hy
  by_contra hh
  push Not at hh
  have hyn : y∉t := by
    intro hyt
    have H := hh y hyt
    simp only [sub_self,norm_zero] at H
    linarith
  have hP : P (insert y t) := by
    constructor
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl|hx
      · exact hy
      · exact ht.1 hx
    · intro x hx z hz hxz
      by_cases hxy : x=y
      · subst x
        have hz' : z∈t := (Finset.mem_insert.mp hz).resolve_left (Ne.symm hxz)
        exact hh z hz'
      · have hx' : x∈t := (Finset.mem_insert.mp hx).resolve_left hxy
        by_cases hzy : z=y
        · subst z
          simpa only [norm_sub_rev] using hh x hx'
        · have hz' : z∈t := (Finset.mem_insert.mp hz).resolve_left hzy
          exact ht.2 x hx' z hz' hxz
  have HM := hmax (insert y t).card ⟨insert y t,rfl,hP⟩
  simp only [Finset.card_insert_of_notMem hyn,←htk] at HM
  omega

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_SpectralTheory_BindingBump
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

theorem bindingCutoff_smooth (n : ℕ) : ContDiff ℝ ∞ (bindingCutoff n) := by
  exact contDiff_prod fun i _ => bindingBump.contDiff.comp (contDiff_apply ℝ Position i)

theorem bindingCutoff_symmetric (n : ℕ) (p : Equiv.Perm (Fin n))
    (x : Configuration n) : bindingCutoff n (x ∘ p) = bindingCutoff n x := by
  exact Equiv.prod_comp p (fun i => bindingBump (x i))

theorem bindingCutoff_nonneg (n : ℕ) (x : Configuration n) : 0 ≤ bindingCutoff n x :=
  Finset.prod_nonneg fun _ _ => bindingBump.nonneg

theorem bindingCutoff_le_one (n : ℕ) (x : Configuration n) : bindingCutoff n x ≤ 1 := by
  exact Finset.prod_le_one (fun _ _ => bindingBump.nonneg) (fun _ _ => bindingBump.le_one)

theorem bindingCutoff_eq_one {n : ℕ} {x : Configuration n} (hx : ‖x‖ ≤ 1) :
    bindingCutoff n x = 1 := by
  apply Finset.prod_eq_one
  intro i _
  apply bindingBump.one_of_mem_closedBall
  simpa [bindingBump, Metric.mem_closedBall, dist_zero_right] using
    (norm_le_pi_norm x i).trans hx

theorem bindingCutoff_eq_zero {n : ℕ} {x : Configuration n} (hx : 2 < ‖x‖) :
    bindingCutoff n x = 0 := by
  have he : ∃ i : Fin n, 2 < ‖x i‖ := by
    by_contra! h
    exact (not_lt_of_ge ((pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 2)).mpr h)) hx
  obtain ⟨i, hi⟩ := he
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (bindingBump.zero_of_le_dist (by simpa [bindingBump] using hi.le))

theorem bindingCutoff_compact (n : ℕ) : HasCompactSupport (bindingCutoff n) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Configuration n) 2)
  intro x hx
  apply bindingCutoff_eq_zero
  simpa [Metric.mem_closedBall, dist_zero_right] using hx

theorem bindingCutoff_derivative_bounded (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖fderiv ℝ (bindingCutoff n) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (bindingCutoff_smooth n).continuous_fderiv (by simp)
    |>.bounded_above_of_compact_support ((bindingCutoff_compact n).fderiv ℝ)
  exact ⟨C, (norm_nonneg _).trans (hC 0), hC⟩

theorem bindingScale_pos (k : ℕ) : 0 < bindingScale k :=
  inv_pos.mpr (by positivity)

theorem bindingScale_le_one (k : ℕ) : bindingScale k ≤ 1 := by
  apply inv_le_one_of_one_le₀
  have := Nat.cast_nonneg (α := ℝ) k
  linarith

theorem bindingScale_tendsto : Tendsto bindingScale atTop (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

theorem expandingCutoff_smooth (n k : ℕ) : ContDiff ℝ ∞ (expandingCutoff n k) := by
  apply (bindingCutoff_smooth n).comp
  exact (contDiff_const (c := bindingScale k)).smul contDiff_id

theorem expandingCutoff_nonneg (n k : ℕ) (x : Configuration n) :
    0 ≤ expandingCutoff n k x := bindingCutoff_nonneg _ _

theorem expandingCutoff_le_one (n k : ℕ) (x : Configuration n) :
    expandingCutoff n k x ≤ 1 := bindingCutoff_le_one _ _

theorem expandingCutoff_fderiv (n k : ℕ) (x v : Configuration n) :
    fderiv ℝ (expandingCutoff n k) x v =
      bindingScale k * fderiv ℝ (bindingCutoff n) (bindingScale k • x) v := by
  have hf := ((bindingCutoff_smooth n).differentiable (by simp) (bindingScale k • x)).hasFDerivAt
  have hc := (hasFDerivAt_id (𝕜 := ℝ) x).const_smul (bindingScale k)
  have hh := (hf.comp x hc).fderiv
  change fderiv ℝ (bindingCutoff n ∘ fun x => bindingScale k • x) x v = _
  rw [hh]
  simp

theorem expandingCutoff_multiplier (n k : ℕ) : SmoothMultiplier (expandingCutoff n k) := by
  refine ⟨expandingCutoff_smooth n k, ?_, ⟨1, fun x => ?_⟩, ?_⟩
  · intro p x
    exact bindingCutoff_symmetric n p (bindingScale k • x)
  · rw [abs_of_nonneg (expandingCutoff_nonneg _ _ _)]
    exact expandingCutoff_le_one _ _ _
  · intro i a
    obtain ⟨C, hC, hb⟩ := bindingCutoff_derivative_bounded n
    refine ⟨C*‖coordinateDirection i a‖, fun x => ?_⟩
    rw [expandingCutoff_fderiv, abs_mul, abs_of_pos (bindingScale_pos k)]
    calc
      bindingScale k * |fderiv ℝ (bindingCutoff n) (bindingScale k • x)
          (coordinateDirection i a)| ≤
          1*(C*‖coordinateDirection i a‖) := by
        apply mul_le_mul (bindingScale_le_one k) _ (abs_nonneg _) (by norm_num)
        exact ((fderiv ℝ (bindingCutoff n) (bindingScale k • x)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _))
      _ = _ := one_mul _

theorem expandingCutoff_tendsto (n : ℕ) (x : Configuration n) :
    Tendsto (fun k => expandingCutoff n k x) atTop (𝓝 1) := by
  have ht := ((bindingCutoff_smooth n).continuous.tendsto 0).comp
    (by simpa using bindingScale_tendsto.smul_const x)
  simpa [Function.comp_def, expandingCutoff, bindingCutoff_eq_one (by simp : ‖(0 : Configuration n)‖ ≤ 1)] using ht

theorem expandingCutoff_fderiv_tendsto (n : ℕ) (x v : Configuration n) :
    Tendsto (fun k => fderiv ℝ (expandingCutoff n k) x v) atTop (𝓝 0) := by
  simp_rw [expandingCutoff_fderiv]
  have ht := (((bindingCutoff_smooth n).continuous_fderiv (by simp)).clm_apply
    (continuous_const (y := v))).tendsto 0 |>.comp (by simpa using bindingScale_tendsto.smul_const x)
  simpa using bindingScale_tendsto.mul ht

theorem expandingCutoff_eq_zero {n k : ℕ} {x : Configuration n}
    (hx : 2*((k:ℝ)+1) < ‖x‖) : expandingCutoff n k x = 0 := by
  apply bindingCutoff_eq_zero
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (bindingScale_pos k)]
  dsimp [bindingScale]
  rw [← div_eq_inv_mul]
  exact (lt_div_iff₀ (by positivity)).mpr hx

theorem expandingCutoff_derivative_uniform_bound (n : ℕ) (i : Fin n) (a : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k x,
      |fderiv ℝ (expandingCutoff n k) x (coordinateDirection i a)| ≤ C := by
  obtain ⟨C, hC, hb⟩ := bindingCutoff_derivative_bounded n
  refine ⟨C*‖coordinateDirection i a‖, mul_nonneg hC (norm_nonneg _), fun k x => ?_⟩
  rw [expandingCutoff_fderiv, abs_mul, abs_of_pos (bindingScale_pos k)]
  calc
    _ ≤ 1*(C*‖coordinateDirection i a‖) := by
      apply mul_le_mul (bindingScale_le_one k) _ (abs_nonneg _) (by norm_num)
      exact ((fderiv ℝ (bindingCutoff n) (bindingScale k • x)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _))
    _ = _ := one_mul _

theorem integral_expandingCutoff_sq_tendsto {n : ℕ} {f : Configuration n → ℝ}
    (hf : Integrable f) :
    Tendsto (fun k => ∫ x, (expandingCutoff n k x)^2 * f x) atTop (𝓝 (∫ x, f x)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
  · intro k
    exact ((expandingCutoff_smooth n k).continuous.aestronglyMeasurable.pow 2).mul
      hf.aestronglyMeasurable
  · exact hf.norm
  · intro k
    exact Eventually.of_forall fun x => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀
        (expandingCutoff_nonneg _ _ _) (expandingCutoff_le_one _ _ _))
  · exact Eventually.of_forall fun x => by
      simpa using ((expandingCutoff_tendsto n x).pow 2).mul_const (f x)

theorem normSquared_cutoff_tendsto {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) :
    Tendsto (fun k => normSquared (multiplyWavefunction (expandingCutoff n k) ψ))
      atTop (𝓝 (normSquared ψ)) := by
  simp only [normSquared, norm_multiplyWavefunction_sq]
  exact tendsto_finsetSum _ fun σ _ =>
    integral_expandingCutoff_sq_tendsto (hd.2.2.1 σ).norm.integrable_sq

theorem kinetic_cutoff_tendsto {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (σ : Spins n) (i : Fin n) (a : Fin 3) :
    Tendsto (fun k => ∫ x, ‖multiplyGradient (expandingCutoff n k) ψ g σ i a x‖^2)
      atTop (𝓝 (∫ x, ‖g σ i a x‖^2)) := by
  obtain ⟨C, hC, hb⟩ := expandingCutoff_derivative_uniform_bound n i a
  apply tendsto_integral_of_dominated_convergence
    (fun x => 2*C^2*‖ψ σ x‖^2 + 2*‖g σ i a x‖^2)
  · intro k
    exact ((hd.multiply (expandingCutoff_multiplier n k)).2.2.2.1 σ i a).norm.aestronglyMeasurable.pow 2
  · exact ((hd.2.2.1 σ).norm.integrable_sq.const_mul (2*C^2)).add
      ((hd.2.2.2.1 σ i a).norm.integrable_sq.const_mul 2)
  · intro k
    exact Eventually.of_forall fun x => by
      have h1 : ‖multiplyGradient (expandingCutoff n k) ψ g σ i a x‖ ≤
          C*‖ψ σ x‖+‖g σ i a x‖ := by
        unfold multiplyGradient
        apply (norm_add_le _ _).trans
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (expandingCutoff_nonneg _ _ _)]
        exact add_le_add (mul_le_mul_of_nonneg_right (hb k x) (norm_nonneg _))
          (mul_le_of_le_one_left (norm_nonneg _) (expandingCutoff_le_one _ _ _))
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith [sq_nonneg (C*‖ψ σ x‖-‖g σ i a x‖)]
  · exact Eventually.of_forall fun x => by
      have h1 := (expandingCutoff_fderiv_tendsto n x (coordinateDirection i a)).smul_const (ψ σ x)
      have h2 := (expandingCutoff_tendsto n x).smul_const (g σ i a x)
      simpa [multiplyGradient] using (h1.add h2).norm.pow 2

theorem energy_cutoff_tendsto {n : ℕ} (Z : ℕ) {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) :
    Tendsto (fun k => energy Z (multiplyWavefunction (expandingCutoff n k) ψ)
      (multiplyGradient (expandingCutoff n k) ψ g)) atTop (𝓝 (energy Z ψ g)) := by
  apply Tendsto.add
  · apply Tendsto.const_mul
    exact tendsto_finsetSum _ fun σ _ => tendsto_finsetSum _ fun i _ =>
      tendsto_finsetSum _ fun a _ => kinetic_cutoff_tendsto hd σ i a
  · apply tendsto_finsetSum
    intro σ _
    have h := integral_expandingCutoff_sq_tendsto (hd.integrable_potential Z σ)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext k
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp only; rw [norm_multiplyWavefunction_sq]; ring

theorem expandingCutoff_fderiv_eq_zero {n k : ℕ} {x : Configuration n}
    (hx : 2*((k:ℝ)+1) < ‖x‖) : fderiv ℝ (expandingCutoff n k) x = 0 := by
  have he : expandingCutoff n k =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
    exact expandingCutoff_eq_zero hy
  simpa using he.fderiv_eq

theorem FormDomain.exists_compact_approximation {n : ℕ} (Z : ℕ)
    {ψ : Wavefunction n} {g : Gradient n} (hd : FormDomain ψ g)
    (hn : normSquared ψ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ (R : ℝ) (χ : Wavefunction n) (h : Gradient n), 0 < R ∧
      FormDomain χ h ∧ normSquared χ = 1 ∧ energy Z χ h < energy Z ψ g + ε ∧
      (∀ σ x, R < ‖x‖ → χ σ x = 0) ∧
      (∀ σ i a x, R < ‖x‖ → h σ i a x = 0) := by
  let χ : ℕ → Wavefunction n := fun k => multiplyWavefunction (expandingCutoff n k) ψ
  let h : ℕ → Gradient n := fun k => multiplyGradient (expandingCutoff n k) ψ g
  let c : ℕ → ℝ := fun k => (Real.sqrt (normSquared (χ k)))⁻¹
  have hnorm : Tendsto (fun k => normSquared (χ k)) atTop (𝓝 1) := by
    simpa [hn] using normSquared_cutoff_tendsto hd
  have hc : Tendsto c atTop (𝓝 1) := by
    have ht := (Real.continuous_sqrt.tendsto 1).comp hnorm
    have hi := ht.inv₀ (by norm_num : Real.sqrt (1 : ℝ) ≠ 0)
    simpa [c] using hi
  have he : Tendsto (fun k => energy Z (scaleWavefunction (c k) (χ k))
      (scaleGradient (c k) (h k))) atTop (𝓝 (energy Z ψ g)) := by
    simp_rw [energy_scale]
    simpa only [one_pow, one_mul] using (hc.pow 2).mul (energy_cutoff_tendsto Z hd)
  have hpos : ∀ᶠ k in atTop, 0 < normSquared (χ k) :=
    hnorm.eventually (Ioi_mem_nhds (by norm_num))
  have hclose : ∀ᶠ k in atTop, energy Z (scaleWavefunction (c k) (χ k))
      (scaleGradient (c k) (h k)) < energy Z ψ g + ε :=
    he.eventually (Iio_mem_nhds (lt_add_of_pos_right _ hε))
  obtain ⟨k, hkpos, hkclose⟩ := (hpos.and hclose).exists
  refine ⟨2*((k:ℝ)+1), scaleWavefunction (c k) (χ k), scaleGradient (c k) (h k),
    by positivity, (hd.multiply (expandingCutoff_multiplier n k)).scale _, ?_, hkclose, ?_, ?_⟩
  · rw [normSquared_scale]
    dsimp [c]
    rw [inv_pow, Real.sq_sqrt hkpos.le, inv_mul_cancel₀ hkpos.ne']
  · intro σ x hx
    simp [scaleWavefunction, χ, multiplyWavefunction, expandingCutoff_eq_zero hx]
  · intro σ i a x hx
    simp [scaleGradient, h, multiplyGradient, expandingCutoff_eq_zero hx,
      expandingCutoff_fderiv_eq_zero hx]

theorem memLp_two_real_tensor {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SFinite μ] [SFinite ν]
    {f : A → ℝ} {g : B → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 ν) :
    MemLp (fun z : A×B => f z.1 • g z.2) 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq_norm
    (hf.aestronglyMeasurable.comp_fst.smul hg.aestronglyMeasurable.comp_snd)).mpr
  change Integrable (fun z : A×B => ‖f z.1 • g z.2‖^2) (μ.prod ν)
  simpa only [norm_smul, mul_pow] using
    hf.norm.integrable_sq.mul_prod hg.norm.integrable_sq

section ProductWeakDerivative
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)] [MeasureSpace F] [BorelSpace F]
  [Measure.IsAddHaarMeasure (volume : Measure F)] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ F] in
theorem compact_support_partial_right {φ : E×F → ℝ}
    (hφ : HasCompactSupport φ) (y : E) : HasCompactSupport (fun x => φ (y,x)) := by
  apply hφ.comp_isClosedEmbedding
  refine ⟨isEmbedding_prodMkRight y, ?_⟩
  have he : Set.range (Prod.mk y : F → E×F) = {y} ×ˢ Set.univ := by
    ext ⟨a,b⟩
    simp [eq_comm]
  rw [he]
  exact isClosed_singleton.prod isClosed_univ

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)] [MeasureSpace F] [BorelSpace F]
  [Measure.IsAddHaarMeasure (volume : Measure F)] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ F] in
theorem compact_support_partial_left {φ : E×F → ℝ}
    (hφ : HasCompactSupport φ) (x : F) : HasCompactSupport (fun y => φ (y,x)) := by
  apply hφ.comp_isClosedEmbedding
  refine ⟨isEmbedding_prodMkLeft x, ?_⟩
  have he : Set.range (fun y : E => (y,x)) = Set.univ ×ˢ {x} := by
    ext ⟨a,b⟩
    simp [eq_comm]
  rw [he]
  exact isClosed_univ.prod isClosed_singleton

omit [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem fderiv_partial_right {φ : E×F → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (y : E) (x v : F) : fderiv ℝ (fun z => φ (y,z)) x v =
      fderiv ℝ φ (y,x) (0,v) := by
  have hc := (hasFDerivAt_const (𝕜 := ℝ) y x).prodMk (hasFDerivAt_id x)
  exact congrArg (fun A : F →L[ℝ] ℝ => A v)
    (((hφ.differentiable (by simp) (y,x)).hasFDerivAt.comp x hc).fderiv)

omit [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem fderiv_partial_left {φ : E×F → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (y v : E) (x : F) : fderiv ℝ (fun z => φ (z,x)) y v =
      fderiv ℝ φ (y,x) (v,0) := by
  have hc := (hasFDerivAt_id (𝕜 := ℝ) y).prodMk (hasFDerivAt_const x y)
  exact congrArg (fun A : E →L[ℝ] ℝ => A v)
    (((hφ.differentiable (by simp) (y,x)).hasFDerivAt.comp y hc).fderiv)

theorem WeakDirectionalDerivative.tensor_right {ψ g : F → ℂ} {v : F}
    (hd : WeakDirectionalDerivative ψ g v) (hψ : MemLp ψ 2 volume) (hg : MemLp g 2 volume)
    {f : E → ℝ} (hf : MemLp f 2 volume) :
    WeakDirectionalDerivative (fun z : E×F => f z.1 • ψ z.2)
      (fun z : E×F => f z.1 • g z.2) (0,v) := by
  intro φ hφ hφc
  dsimp only
  have hLp := memLp_two_real_tensor hf hψ
  have hgLp := memLp_two_real_tensor hf hg
  have hi₁ : Integrable (fun z : E×F => fderiv ℝ φ z (0,v) • (f z.1 • ψ z.2)) :=
    (hLp.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const) (hφc.fderiv_apply ℝ _)
  have hi₂ : Integrable (fun z : E×F => φ z • (f z.1 • g z.2)) :=
    (hgLp.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      hφ.continuous hφc
  change (∫ z : E×F, fderiv ℝ φ z (0,v) • (f z.1 • ψ z.2) ∂(volume.prod volume)) =
    -(∫ z : E×F, φ z • (f z.1 • g z.2) ∂(volume.prod volume))
  rw [integral_prod _ hi₁, integral_prod _ hi₂, ← integral_neg]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    have hs := hd (fun x => φ (y,x)) (hφ.comp (contDiff_const.prodMk contDiff_id))
      (compact_support_partial_right hφc y)
    simp_rw [fderiv_partial_right hφ y] at hs
    simp_rw [smul_comm _ (f y), integral_smul]
    simpa only [smul_neg] using congrArg (fun z : ℂ => f y • z) hs

theorem smooth_tensor_weak_left {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfLp : MemLp f 2 volume) (u : E)
    (hdfLp : MemLp (fun y => fderiv ℝ f y u) 2 volume)
    {ψ : F → ℂ} (hψ : MemLp ψ 2 volume) :
    WeakDirectionalDerivative (fun z : E×F => f z.1 • ψ z.2)
      (fun z : E×F => fderiv ℝ f z.1 u • ψ z.2) (u,0) := by
  intro φ hφ hφc
  dsimp only
  have hLp := memLp_two_real_tensor hfLp hψ
  have hgLp := memLp_two_real_tensor hdfLp hψ
  have hi₁ : Integrable (fun z : E×F => fderiv ℝ φ z (u,0) • (f z.1 • ψ z.2)) :=
    (hLp.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const) (hφc.fderiv_apply ℝ _)
  have hi₂ : Integrable (fun z : E×F => φ z • (fderiv ℝ f z.1 u • ψ z.2)) :=
    (hgLp.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      hφ.continuous hφc
  change (∫ z : E×F, fderiv ℝ φ z (u,0) • (f z.1 • ψ z.2) ∂(volume.prod volume)) =
    -(∫ z : E×F, φ z • (fderiv ℝ f z.1 u • ψ z.2) ∂(volume.prod volume))
  rw [integral_prod_symm _ hi₁, integral_prod_symm _ hi₂, ← integral_neg]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    let φx : E → ℝ := fun y => φ (y,x)
    have hs : ContDiff ℝ ∞ φx := hφ.comp (contDiff_id.prodMk contDiff_const)
    have hsc : HasCompactSupport φx := compact_support_partial_left hφc x
    have hfd : Continuous (fun y => fderiv ℝ φx y u) :=
      (hs.continuous_fderiv (by simp)).clm_apply continuous_const
    have hid : Integrable (fun y => fderiv ℝ φx y u * f y) :=
      (hfLp.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
        hfd (hsc.fderiv_apply ℝ _)
    have hid' : Integrable (fun y => fderiv ℝ f y u * φx y) := by
      simpa only [smul_eq_mul, mul_comm] using
        (hdfLp.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
          hs.continuous hsc
    have hi : Integrable (fun y => f y * φx y) := by
      simpa only [smul_eq_mul, mul_comm] using
        (hfLp.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
          hs.continuous hsc
    have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := u)
      hid' (by simpa only [mul_comm] using hid) hi
      (fun y _ => hf.differentiable (by simp) y) (fun y _ => hs.differentiable (by simp) y)
    have hh' : (∫ y, fderiv ℝ φ (y,x) (u,0) * f y) =
        -(∫ y, φ (y,x) * fderiv ℝ f y u) := by
      simpa only [φx, fderiv_partial_left hφ, mul_comm] using hh
    simp_rw [smul_smul]
    rw [integral_smul_const, integral_smul_const, hh', neg_smul]

omit [Measure.IsAddHaarMeasure (volume : Measure E)]
  [Measure.IsAddHaarMeasure (volume : Measure F)]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem WeakDirectionalDerivative.comp_equiv {ψ g : F → ℂ} {v : F}
    (hd : WeakDirectionalDerivative ψ g v) (e : E ≃L[ℝ] F)
    (he : MeasurePreserving e) :
    WeakDirectionalDerivative (ψ ∘ e) (g ∘ e) (e.symm v) := by
  intro φ hφ hφc
  have hc := hφ.comp e.symm.contDiff
  have hcc : HasCompactSupport (φ ∘ e.symm) :=
    hφc.comp_homeomorph e.symm.toHomeomorph
  have hdφ : ∀ y, fderiv ℝ (φ ∘ e.symm) y v = fderiv ℝ φ (e.symm y) (e.symm v) := by
    intro y
    rw [((hφ.differentiable (by simp) (e.symm y)).hasFDerivAt.comp y
      e.symm.hasFDerivAt).fderiv]
    rfl
  have hint := hd (φ ∘ e.symm) hc hcc
  simp_rw [hdφ] at hint
  dsimp only [Function.comp_apply] at hint
  rw [← he.integral_comp e.toHomeomorph.measurableEmbedding
      (fun y => fderiv ℝ φ (e.symm y) (e.symm v) • ψ y),
    ← he.integral_comp e.toHomeomorph.measurableEmbedding
      (fun y => φ (e.symm y) • g y)] at hint
  simpa only [ContinuousLinearEquiv.symm_apply_apply, Function.comp_apply] using hint

end ProductWeakDerivative

end NeutralAtom
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_ConfigurationSplit
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

 theorem configurationSplit_preserving (n : ℕ) : MeasurePreserving (configurationSplit n) := by
  have h := volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => Position) 0
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  change (x 0, fun i => x i.succ) = (x 0, fun i => x (Fin.succAbove 0 i))
  simp only [Fin.succAbove_zero]

 theorem configurationPerm_preserving {n : ℕ} (p : Equiv.Perm (Fin n)) :
    MeasurePreserving (configurationPerm p) :=
  (volume_measurePreserving_piCongrLeft (fun _ : Fin n => Position) p).symm
    (MeasurableEquiv.piCongrLeft (fun _ : Fin n => Position) p)

 theorem configurationPerm_symm_direction {n : ℕ} (p : Equiv.Perm (Fin n))
    (i : Fin n) (a : Fin 3) :
    (configurationPerm p).symm (coordinateDirection (p.symm i) a) = coordinateDirection i a := by
  rw [← configurationPerm_direction, ContinuousLinearEquiv.symm_apply_apply]

 theorem HasWeakGradient.permute {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hg : HasWeakGradient ψ g) (p : Equiv.Perm (Fin n)) :
    HasWeakGradient (permuteWavefunction p ψ) (permuteGradient p g) := by
  intro σ i a φ hφ hφc
  have hd : WeakDirectionalDerivative (ψ (σ ∘ p)) (g (σ ∘ p) (p.symm i) a)
      (coordinateDirection (p.symm i) a) := by
    intro η hη hηc
    simpa only [Complex.real_smul, Complex.ofReal_mul] using hg (σ ∘ p) (p.symm i) a η hη hηc
  have ht := hd.comp_equiv (configurationPerm p) (configurationPerm_preserving p)
  rw [configurationPerm_symm_direction] at ht
  simpa only [permuteWavefunction, permuteGradient, Function.comp_apply,
    configurationPerm_apply, Complex.real_smul, Complex.ofReal_mul] using ht φ hφ hφc

 theorem half_ordered_sum {n : ℕ} (F : Fin n → Fin n → ℝ)
    (hF : ∀ i j, F i j = F j i) (hdiag : ∀ i, F i i = 0) :
    (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => i < j), F i j) =
      (1/2:ℝ) * ∑ i : Fin n, ∑ j : Fin n, F i j := by
  classical
  have he : ∀ i j, F i j = (if i < j then F i j else 0) + (if j < i then F j i else 0) := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [hij, not_lt.mpr hij.le]
    · simp [hdiag]
    · simp [hji, not_lt.mpr hji.le, hF]
  have hs : (∑ i : Fin n, ∑ j : Fin n, F i j) =
      2 * (∑ i : Fin n, ∑ j : Fin n, if i < j then F i j else 0) := by
    conv_lhs => arg 2; ext i; arg 2; ext j; rw [he i j]
    simp_rw [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => if j < i then F j i else 0)]
    ring
  simp only [Finset.sum_filter]
  rw [hs]
  ring

 theorem coulombPotential_permute {n : ℕ} (Z : ℕ) (p : Equiv.Perm (Fin n))
    (x : Configuration n) : coulombPotential Z (x ∘ p) = coulombPotential Z x := by
  have hn : (∑ i : Fin n, ‖x (p i)‖⁻¹) = ∑ i : Fin n, ‖x i‖⁻¹ :=
    Equiv.sum_comp p (fun i => ‖x i‖⁻¹)
  have hs (y : Configuration n) :
      (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => i < j), ‖y i-y j‖⁻¹) =
      (1/2:ℝ) * ∑ i : Fin n, ∑ j : Fin n, ‖y i-y j‖⁻¹ :=
    half_ordered_sum _ (fun i j => by rw [norm_sub_rev]) (fun i => by simp)
  have hp : (∑ i : Fin n, ∑ j : Fin n, ‖x (p i)-x (p j)‖⁻¹) =
      ∑ i : Fin n, ∑ j : Fin n, ‖x i-x j‖⁻¹ := by
    calc
      _ = ∑ i : Fin n, ∑ j : Fin n, ‖x (p i)-x j‖⁻¹ := by
        apply Finset.sum_congr rfl
        intro i _
        exact Equiv.sum_comp p (fun j => ‖x (p i)-x j‖⁻¹)
      _ = _ := Equiv.sum_comp p (fun i => ∑ j : Fin n, ‖x i-x j‖⁻¹)
  simp only [coulombPotential, hs, Function.comp_apply, hn, hp]

 theorem HasWeakGradient.insert {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hg : HasWeakGradient ψ g) (hψ : ∀ σ, MemLp (ψ σ) 2 volume)
    (hgLp : ∀ σ i a, MemLp (g σ i a) 2 volume) {f : Position → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfLp : MemLp f 2 volume)
    (hdfLp : ∀ a : Fin 3, MemLp (fun y => fderiv ℝ f y (EuclideanSpace.single a 1)) 2 volume) :
    HasWeakGradient (insertWavefunction f ψ) (insertGradient f ψ g) := by
  intro σ i a φ hφ hφc
  by_cases hσ : σ 0 = 0
  · let τ : Spins n := fun j => σ j.succ
    cases i using Fin.cases with
    | zero =>
      have ht := (smooth_tensor_weak_left hf hfLp (EuclideanSpace.single a 1) (hdfLp a)
        (hψ τ)).comp_equiv (configurationSplit n) (configurationSplit_preserving n)
      have hv : (configurationSplit n).symm (EuclideanSpace.single a 1, 0) =
          coordinateDirection 0 a := by
        apply (configurationSplit n).injective
        rw [ContinuousLinearEquiv.apply_symm_apply, configurationSplit_direction_zero]
      rw [hv] at ht
      simpa only [insertWavefunction, insertGradient, hσ, ↓reduceIte, Fin.cases_zero,
        configurationSplit_apply, Function.comp_apply, Complex.real_smul] using ht φ hφ hφc
    | succ i =>
      have hd : WeakDirectionalDerivative (ψ τ) (g τ i a) (coordinateDirection i a) := by
        intro η hη hηc
        simpa only [Complex.real_smul] using hg τ i a η hη hηc
      have ht := (hd.tensor_right (hψ τ) (hgLp τ i a) hfLp).comp_equiv
        (configurationSplit n) (configurationSplit_preserving n)
      have hv : (configurationSplit n).symm (0, coordinateDirection i a) =
          coordinateDirection i.succ a := by
        apply (configurationSplit n).injective
        rw [ContinuousLinearEquiv.apply_symm_apply, configurationSplit_direction_succ]
      rw [hv] at ht
      simpa only [insertWavefunction, insertGradient, hσ, ↓reduceIte, Fin.cases_succ,
        configurationSplit_apply, Function.comp_apply, Complex.real_smul] using ht φ hφ hφc
  · simp [insertWavefunction, insertGradient, hσ]

 theorem insertWavefunction_memLp {n : ℕ} {ψ : Wavefunction n} (hψ : ∀ σ, MemLp (ψ σ) 2 volume)
    {f : Position → ℝ} (hf : MemLp f 2 volume) (σ : Spins (n+1)) :
    MemLp (insertWavefunction f ψ σ) 2 volume := by
  by_cases hσ : σ 0 = 0
  · have he : insertWavefunction f ψ σ =
        (fun z : Position×Configuration n => f z.1 • ψ (fun i => σ i.succ) z.2) ∘
          configurationSplit n := by
      funext x
      simp [insertWavefunction, hσ]
    rw [he]
    exact (memLp_two_real_tensor hf (hψ (fun i => σ i.succ))).comp_measurePreserving
      (configurationSplit_preserving n)
  · have he : insertWavefunction f ψ σ = fun _ => 0 := by
      funext x
      simp [insertWavefunction, hσ]
    rw [he]
    exact MemLp.zero'

 theorem insertGradient_memLp {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hg : ∀ σ i a, MemLp (g σ i a) 2 volume)
    {f : Position → ℝ} (hf : MemLp f 2 volume)
    (hdf : ∀ a : Fin 3, MemLp (fun y => fderiv ℝ f y (EuclideanSpace.single a 1)) 2 volume)
    (σ : Spins (n+1)) (i : Fin (n+1)) (a : Fin 3) :
    MemLp (insertGradient f ψ g σ i a) 2 volume := by
  by_cases hσ : σ 0 = 0
  · cases i using Fin.cases with
    | zero =>
      have he : insertGradient f ψ g σ 0 a =
          (fun z : Position×Configuration n => fderiv ℝ f z.1 (EuclideanSpace.single a 1) •
            ψ (fun j => σ j.succ) z.2) ∘ configurationSplit n := by
        funext x
        simp [insertGradient, hσ]
      rw [he]
      exact (memLp_two_real_tensor (hdf a) (hψ (fun j => σ j.succ))).comp_measurePreserving
        (configurationSplit_preserving n)
    | succ i =>
      have he : insertGradient f ψ g σ i.succ a =
          (fun z : Position×Configuration n => f z.1 •
            g (fun j => σ j.succ) i a z.2) ∘ configurationSplit n := by
        funext x
        simp [insertGradient, hσ]
      rw [he]
      exact (memLp_two_real_tensor hf (hg (fun j => σ j.succ) i a)).comp_measurePreserving
        (configurationSplit_preserving n)
  · have he : insertGradient f ψ g σ i a = fun _ => 0 := by
      funext x
      simp [insertGradient, hσ]
    rw [he]
    exact MemLp.zero'

 theorem integral_tensor_norm {n : ℕ} (f : Position → ℝ) (ψ : Configuration n → ℂ) :
    (∫ x : Configuration (n+1), ‖f (x 0) • ψ (fun i => x i.succ)‖^2) =
      (∫ y : Position, (f y)^2) * ∫ x : Configuration n, ‖ψ x‖^2 := by
  have he := (configurationSplit_preserving n).integral_comp
    (configurationSplit n).toHomeomorph.measurableEmbedding
    (fun z : Position × Configuration n => ‖f z.1 • ψ z.2‖^2)
  change (∫ x : Configuration (n+1), ‖f (x 0) • ψ (fun i => x i.succ)‖^2) =
    ∫ z : Position × Configuration n, ‖f z.1 • ψ z.2‖^2 at he
  rw [he]
  simp_rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  exact integral_prod_mul (μ := volume) (ν := volume)
    (fun y : Position => (f y)^2) (fun x : Configuration n => ‖ψ x‖^2)

 theorem normSquared_insert {n : ℕ} (f : Position → ℝ) (ψ : Wavefunction n) :
    normSquared (insertWavefunction f ψ) = (∫ y : Position, (f y)^2) * normSquared ψ := by
  classical
  unfold normSquared
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => Fin 2))]
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, insertWavefunction, Fin.cons_zero,
    Fin.cons_succ, h10, ↓reduceIte]
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), integral_zero,
    Finset.sum_const_zero, add_zero, integral_tensor_norm, Finset.mul_sum]

 theorem FormRegular.pair {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (h : FormRegular ψ g) (σ : Spins n) (i j : Fin n) :
    Integrable (fun x : Configuration n => ‖x i-x j‖⁻¹ * ‖ψ σ x‖^2) := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact h.2.2.2.2 σ i j hij
  · simp
  · simpa only [norm_sub_rev] using h.2.2.2.2 σ j i hji

 theorem FormRegular.permute {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (h : FormRegular ψ g) (p : Equiv.Perm (Fin n)) :
    FormRegular (permuteWavefunction p ψ) (permuteGradient p g) := by
  refine ⟨h.1.permute p, ?_, ?_, ?_, ?_⟩
  · intro σ
    exact (h.2.1 (σ ∘ p)).comp_measurePreserving (configurationPerm_preserving p)
  · intro σ i a
    exact (h.2.2.1 (σ ∘ p) (p.symm i) a).comp_measurePreserving (configurationPerm_preserving p)
  · intro σ i
    have ht := (configurationPerm_preserving p).integrable_comp_of_integrable
      (h.2.2.2.1 (σ ∘ p) (p.symm i))
    simpa only [Function.comp_def, configurationPerm_apply, Equiv.apply_symm_apply,
      permuteWavefunction] using ht
  · intro σ i j _
    have ht := (configurationPerm_preserving p).integrable_comp_of_integrable
      (h.pair (σ ∘ p) (p.symm i) (p.symm j))
    simpa only [Function.comp_def, configurationPerm_apply, Equiv.apply_symm_apply,
      permuteWavefunction] using ht

 theorem WeakDirectionalDerivative.finite_sum {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] (c : ι → ℝ) {ψ g : ι → E → ℂ} {v : E}
    (hd : ∀ i, WeakDirectionalDerivative (ψ i) (g i) v)
    (hψ : ∀ i, MemLp (ψ i) 2 volume) (hg : ∀ i, MemLp (g i) 2 volume) :
    WeakDirectionalDerivative (fun x => ∑ i, c i • ψ i x) (fun x => ∑ i, c i • g i x) v := by
  intro φ hφ hφc
  have hi (i : ι) : Integrable (fun x => fderiv ℝ φ x v • (c i • ψ i x)) :=
    ((hψ i).const_smul (c i)).locallyIntegrable (by norm_num)
      |>.integrable_smul_left_of_hasCompactSupport
        ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const) (hφc.fderiv_apply ℝ _)
  have hi' (i : ι) : Integrable (fun x => φ x • (c i • g i x)) :=
    ((hg i).const_smul (c i)).locallyIntegrable (by norm_num)
      |>.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
  dsimp only
  simp_rw [Finset.smul_sum]
  rw [integral_finsetSum _ (fun i _ => hi i), integral_finsetSum _ (fun i _ => hi' i),
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [smul_comm _ (c i), integral_smul]
  simpa only [smul_neg] using congrArg (fun z : ℂ => c i • z) (hd i φ hφ hφc)

 theorem integrable_weighted_norm_sum {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {ι : Type*} [Fintype ι] {W : A → ℝ} (hW : Measurable W) (hW0 : ∀ x, 0 ≤ W x)
    (c : ι → ℝ) {f : ι → A → ℂ} (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hi : ∀ i, Integrable (fun x => W x * ‖f i x‖^2) μ) :
    Integrable (fun x => W x * ‖∑ i, c i • f i x‖^2) μ := by
  have hroot : Measurable (fun x => Real.sqrt (W x)) := Real.continuous_sqrt.measurable.comp hW
  have he : ∀ i, MemLp (fun x => Real.sqrt (W x) • f i x) 2 μ := by
    intro i
    apply (memLp_two_iff_integrable_sq_norm (hroot.aestronglyMeasurable.smul (hf i))).mpr
    change Integrable (fun x => ‖Real.sqrt (W x) • f i x‖^2) μ
    simpa only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hW0 _)] using hi i
  have hs := memLp_finsetSum Finset.univ (fun i _ => (he i).const_smul (c i))
  have hint := hs.norm.integrable_sq
  have hx : (fun x => ‖∑ i, c i • (Real.sqrt (W x) • f i x)‖^2) =
      (fun x => W x * ‖∑ i, c i • f i x‖^2) := by
    funext x
    simp_rw [smul_comm (c _) (Real.sqrt (W x)), ← Finset.smul_sum]
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hW0 x)]
  exact hx ▸ hint

 theorem FormRegular.finite_sum {n : ℕ} {ι : Type*} [Fintype ι] (c : ι → ℝ)
    {ψ : ι → Wavefunction n} {g : ι → Gradient n} (h : ∀ j, FormRegular (ψ j) (g j)) :
    FormRegular (sumWavefunction c ψ) (sumGradient c g) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro σ i a φ hφ hφc
    have hd (j : ι) : WeakDirectionalDerivative (ψ j σ) (g j σ i a) (coordinateDirection i a) := by
      intro η hη hηc
      simpa only [Complex.real_smul] using (h j).1 σ i a η hη hηc
    simpa only [sumWavefunction, sumGradient, Complex.real_smul] using
      (WeakDirectionalDerivative.finite_sum c hd (fun j => (h j).2.1 σ)
        (fun j => (h j).2.2.1 σ i a)) φ hφ hφc
  · intro σ
    exact memLp_finsetSum Finset.univ (fun j _ => ((h j).2.1 σ).const_smul (c j))
  · intro σ i a
    exact memLp_finsetSum Finset.univ (fun j _ => ((h j).2.2.1 σ i a).const_smul (c j))
  · intro σ i
    exact integrable_weighted_norm_sum (by fun_prop) (fun x => inv_nonneg.mpr (norm_nonneg _)) c
      (fun j => ((h j).2.1 σ).aestronglyMeasurable) (fun j => (h j).2.2.2.1 σ i)
  · intro σ i k hik
    exact integrable_weighted_norm_sum (by fun_prop) (fun x => inv_nonneg.mpr (norm_nonneg _)) c
      (fun j => ((h j).2.1 σ).aestronglyMeasurable) (fun j => (h j).2.2.2.2 σ i k hik)

 theorem antisymmetrize_antisymmetric {n : ℕ} (ψ : Wavefunction n) :
    IsAntisymmetric (antisymmetrize ψ) := by
  intro q σ
  apply Eventually.of_forall
  intro x
  have he (p : Equiv.Perm (Fin n)) :
      permutationSign p = permutationSign q * permutationSign (q*p) := by
    rw [permutationSign_mul, ← mul_assoc, permutationSign_sq, one_mul]
  change (∑ p : Equiv.Perm (Fin n), permutationSign p • ψ ((σ ∘ q) ∘ p) ((x ∘ q) ∘ p)) =
    ((Equiv.Perm.sign q : ℤ) : ℂ) * ∑ p : Equiv.Perm (Fin n),
      permutationSign p • ψ (σ ∘ p) (x ∘ p)
  calc
    _ = ∑ p : Equiv.Perm (Fin n), permutationSign q •
        (permutationSign (q*p) • ψ (σ ∘ (q*p : Equiv.Perm (Fin n))) (x ∘ (q*p : Equiv.Perm (Fin n)))) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [smul_smul, ← he p]
      rfl
    _ = permutationSign q • ∑ p : Equiv.Perm (Fin n),
        permutationSign (q*p) • ψ (σ ∘ (q*p : Equiv.Perm (Fin n))) (x ∘ (q*p : Equiv.Perm (Fin n))) := by rw [Finset.smul_sum]
    _ = permutationSign q • ∑ p : Equiv.Perm (Fin n),
        permutationSign p • ψ (σ ∘ p) (x ∘ p) := by
      exact congrArg (fun z : ℂ => permutationSign q • z)
        (Equiv.sum_comp (Equiv.mulLeft q)
          (fun p : Equiv.Perm (Fin n) => permutationSign p • ψ (σ ∘ p) (x ∘ p)))
    _ = _ := by simp only [permutationSign, Complex.real_smul, Complex.ofReal_intCast]

 theorem configurationTail_quasiPreserving (n : ℕ) :
    Measure.QuasiMeasurePreserving (fun x : Configuration (n+1) => fun i : Fin n => x i.succ)
      volume volume :=
  Measure.quasiMeasurePreserving_snd.comp (configurationSplit_preserving n).quasiMeasurePreserving

 theorem permutationSign_decompose {n : ℕ} (i : Fin (n+1)) (p : Equiv.Perm (Fin n)) :
    permutationSign (Equiv.Perm.decomposeFin.symm (i,p)) =
      permutationSign (Equiv.swap 0 i) * permutationSign p := by
  have he := Equiv.Perm.decomposeFin_symm_of_one i
  rw [← he]
  by_cases hi : i = 0
  · simp [permutationSign, Equiv.Perm.decomposeFin.symm_sign, hi]
  · simp [permutationSign, Equiv.Perm.decomposeFin.symm_sign, hi, Ne.symm hi]

 theorem insert_permute_decompose {n : ℕ} {ψ : Wavefunction n} (hψ : IsAntisymmetric ψ)
    (f : Position → ℝ) (i : Fin (n+1)) (p : Equiv.Perm (Fin n)) (σ : Spins (n+1)) :
    permuteWavefunction (Equiv.Perm.decomposeFin.symm (i,p)) (insertWavefunction f ψ) σ =ᵐ[volume]
      (fun x => permutationSign p • permuteWavefunction (Equiv.swap 0 i) (insertWavefunction f ψ) σ x) := by
  let τ : Spins n := fun j => σ (Equiv.swap 0 i j.succ)
  have hp := (hψ p τ).comp_tendsto
    ((configurationTail_quasiPreserving n).comp
      (configurationPerm_preserving (Equiv.swap 0 i)).quasiMeasurePreserving).tendsto_ae
  filter_upwards [hp] with x hx
  change ψ (τ ∘ p) ((fun j => x (Equiv.swap 0 i j.succ)) ∘ p) =
    ((Equiv.Perm.sign p : ℤ) : ℂ) * ψ τ (fun j => x (Equiv.swap 0 i j.succ)) at hx
  simp only [permuteWavefunction, insertWavefunction, Function.comp_apply,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Equiv.swap_apply_left]
  by_cases hσ : σ i = 0
  · simp only [hσ, ↓reduceIte]
    change f (x i) • ψ (τ ∘ p) ((fun j => x (Equiv.swap 0 i j.succ)) ∘ p) = _
    rw [hx]
    simp only [permutationSign, Complex.real_smul, Complex.ofReal_intCast]
    ring
  · simp [hσ]

end NeutralAtom
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_WedgeInsert
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

 theorem antisymmetrize_insert_eq {n : ℕ} {ψ : Wavefunction n} (hψ : IsAntisymmetric ψ)
    (f : Position → ℝ) (σ : Spins (n+1)) :
    antisymmetrize (insertWavefunction f ψ) σ =ᵐ[volume]
      (fun x => (n.factorial : ℝ) • wedgeInsert f ψ σ x) := by
  classical
  have hi : ∀ᵐ x : Configuration (n+1) ∂volume, ∀ i : Fin (n+1), ∀ p : Equiv.Perm (Fin n),
      permutationSign (Equiv.Perm.decomposeFin.symm (i,p)) •
        permuteWavefunction (Equiv.Perm.decomposeFin.symm (i,p)) (insertWavefunction f ψ) σ x =
      permutationSign (Equiv.swap 0 i) • permuteWavefunction (Equiv.swap 0 i) (insertWavefunction f ψ) σ x := by
    apply (ae_all_iff).mpr
    intro i
    apply (ae_all_iff).mpr
    intro p
    filter_upwards [insert_permute_decompose hψ f i p σ] with x hx
    rw [hx, permutationSign_decompose, smul_smul]
    simp only [mul_assoc, permutationSign_sq, mul_one]
  filter_upwards [hi] with x hx
  unfold antisymmetrize sumWavefunction wedgeInsert
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm]
  rw [Fintype.sum_prod_type]
  simp_rw [hx]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    sumWavefunction, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.real_smul, nsmul_eq_mul, Complex.ofReal_natCast]

 theorem insertionSupport_tensor {n : ℕ} {R : ℝ} {f : Position → ℝ}
    {ψ : Wavefunction n} (hf : ∀ y, ‖y‖ ≤ R → f y = 0)
    (hψ : ∀ σ x, R < ‖x‖ → ψ σ x = 0) :
    InsertionSupport R (insertWavefunction f ψ) := by
  intro σ x hx
  have hi : σ 0 = 0 := by
    by_contra hh
    exact hx (by simp [insertWavefunction, hh])
  have hf0 : f (x 0) ≠ 0 := by
    intro hh
    exact hx (by simp [insertWavefunction, hh])
  have hψ0 : ψ (fun i => σ i.succ) (fun i => x i.succ) ≠ 0 := by
    intro hh
    exact hx (by simp [insertWavefunction, hh])
  have htail : ‖fun i : Fin n => x i.succ‖ ≤ R := by
    by_contra hh
    exact hψ0 (hψ _ _ (lt_of_not_ge hh))
  exact ⟨lt_of_not_ge (fun hh => hf0 (hf _ hh)), fun i => (norm_le_pi_norm _ i).trans htail⟩

 theorem InsertionSupport.swap {n : ℕ} {R : ℝ} {F : Wavefunction (n+1)}
    (hF : InsertionSupport R F) {σ : Spins (n+1)} {x : Configuration (n+1)}
    {i : Fin (n+1)} (hi : permuteWavefunction (Equiv.swap 0 i) F σ x ≠ 0) :
    R < ‖x i‖ ∧ ∀ j, j ≠ i → ‖x j‖ ≤ R := by
  have h := hF (σ ∘ Equiv.swap 0 i) (x ∘ Equiv.swap 0 i) hi
  refine ⟨by simpa only [Function.comp_apply, Equiv.swap_apply_left] using h.1, ?_⟩
  intro j hji
  have hne : Equiv.swap 0 i j ≠ 0 := by
    intro hh
    have he := congrArg (Equiv.swap 0 i) hh
    exact hji (by simpa only [Equiv.swap_apply_self, Equiv.swap_apply_left] using he)
  have hg : ∀ k : Fin (n+1), k ≠ 0 → ‖x (Equiv.swap 0 i k)‖ ≤ R := by
    intro k hk
    cases k using Fin.cases with
    | zero => exact (hk rfl).elim
    | succ k => exact h.2 k
  simpa only [Equiv.swap_apply_self] using hg _ hne

 theorem InsertionSupport.placements_disjoint {n : ℕ} {R : ℝ} {F G : Wavefunction (n+1)}
    (hF : InsertionSupport R F) (hG : InsertionSupport R G) (σ : Spins (n+1))
    (x : Configuration (n+1)) {i j : Fin (n+1)} (hij : i ≠ j) :
    permuteWavefunction (Equiv.swap 0 i) F σ x = 0 ∨
      permuteWavefunction (Equiv.swap 0 j) G σ x = 0 := by
  by_contra hh
  have hi := hF.swap (not_or.mp hh).1
  have hj := hG.swap (not_or.mp hh).2
  exact (not_lt_of_ge (hj.2 i hij)) hi.1

 theorem norm_sq_sum_of_disjoint {ι : Type*} [Fintype ι] (v : ι → ℂ)
    (hv : ∀ i j, i ≠ j → v i = 0 ∨ v j = 0) :
    ‖∑ i, v i‖^2 = ∑ i, ‖v i‖^2 := by
  classical
  by_cases he : ∃ i, v i ≠ 0
  · obtain ⟨i,hi⟩ := he
    have hz : ∀ j, j ≠ i → v j = 0 := fun j hji => (hv j i hji).resolve_right hi
    rw [Finset.sum_eq_single i, Finset.sum_eq_single i]
    · intro j _ hji
      simp [hz j hji]
    · simp
    · intro j _ hji
      exact hz j hji
    · simp
  · have hz : ∀ i, v i = 0 := by simpa using he
    simp [hz]

 theorem normSquared_permute {n : ℕ} (p : Equiv.Perm (Fin n)) (ψ : Wavefunction n) :
    normSquared (permuteWavefunction p ψ) = normSquared ψ := by
  unfold normSquared permuteWavefunction
  have hi (σ : Spins n) := (configurationPerm_preserving p).integral_comp
    (configurationPerm p).toHomeomorph.measurableEmbedding (fun x => ‖ψ (σ ∘ p) x‖^2)
  simp only [configurationPerm_apply] at hi
  simp_rw [hi]
  exact Equiv.sum_comp (spinsPerm p) (fun σ => ∫ x, ‖ψ σ x‖^2)

 theorem energy_permute {n : ℕ} (Z : ℕ) (p : Equiv.Perm (Fin n))
    (ψ : Wavefunction n) (g : Gradient n) :
    energy Z (permuteWavefunction p ψ) (permuteGradient p g) = energy Z ψ g := by
  have hi (σ : Spins n) (i : Fin n) (a : Fin 3) :=
    (configurationPerm_preserving p).integral_comp
      (configurationPerm p).toHomeomorph.measurableEmbedding (fun x => ‖g (σ ∘ p) (p.symm i) a x‖^2)
  simp only [configurationPerm_apply] at hi
  have hv (σ : Spins n) := (configurationPerm_preserving p).integral_comp
    (configurationPerm p).toHomeomorph.measurableEmbedding
    (fun x => coulombPotential Z x * ‖ψ (σ ∘ p) x‖^2)
  simp only [configurationPerm_apply, coulombPotential_permute] at hv
  unfold energy permuteWavefunction permuteGradient
  simp_rw [hi, hv]
  congr 1
  · congr 1
    have hs (σ : Spins n) : (∑ i : Fin n, ∑ a : Fin 3, ∫ x, ‖g σ (p.symm i) a x‖^2) =
        ∑ i : Fin n, ∑ a : Fin 3, ∫ x, ‖g σ i a x‖^2 :=
      Equiv.sum_comp p.symm (fun i => ∑ a : Fin 3, ∫ x, ‖g σ i a x‖^2)
    simp_rw [hs]
    exact Equiv.sum_comp (spinsPerm p) (fun σ => ∑ i : Fin n, ∑ a : Fin 3, ∫ x, ‖g σ i a x‖^2)
  · exact Equiv.sum_comp (spinsPerm p) (fun σ => ∫ x, coulombPotential Z x * ‖ψ σ x‖^2)

 theorem norm_sq_sum_real_smul_of_disjoint {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (v : ι → ℂ) (hv : ∀ i j, i ≠ j → v i = 0 ∨ v j = 0) :
    ‖∑ i, c i • v i‖^2 = ∑ i, (c i)^2 * ‖v i‖^2 := by
  rw [norm_sq_sum_of_disjoint (fun i => c i • v i)]
  · simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  · intro i j hij
    rcases hv i j hij with hi | hj
    · exact Or.inl (by rw [hi, smul_zero])
    · exact Or.inr (by rw [hj, smul_zero])

 theorem FormRegular.integrable_potential {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormRegular ψ g) (Z : ℕ) (σ : Spins n) :
    Integrable (fun x : Configuration n => coulombPotential Z x*‖ψ σ x‖^2) := by
  have hn := integrable_finsetSum Finset.univ (fun i _ => hd.2.2.2.1 σ i)
  have hp := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum (Finset.univ.filter (fun j => i < j))
      (fun j hj => hd.2.2.2.2 σ i j (Finset.mem_filter.mp hj).2))
  apply ((hn.const_mul (-(Z:ℝ))).add hp).congr
  exact Eventually.of_forall fun x => by
    simp only [Pi.add_apply, coulombPotential, add_mul, Finset.sum_mul, mul_assoc]

 theorem normSquared_disjoint_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (c : ι → ℝ) {ψ : ι → Wavefunction n} (hψ : ∀ i σ, MemLp (ψ i σ) 2 volume)
    (hd : ∀ σ x i j, i ≠ j → ψ i σ x = 0 ∨ ψ j σ x = 0) :
    normSquared (sumWavefunction c ψ) = ∑ i, (c i)^2 * normSquared (ψ i) := by
  unfold normSquared sumWavefunction
  simp_rw [norm_sq_sum_real_smul_of_disjoint c _ (hd _ _)]
  simp_rw [integral_finsetSum _ (fun i _ => ((hψ i _).norm.integrable_sq).const_mul ((c i)^2)),
    integral_const_mul]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

 theorem energy_disjoint_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (Z : ℕ) (c : ι → ℝ) {ψ : ι → Wavefunction n} {g : ι → Gradient n}
    (h : ∀ i, FormRegular (ψ i) (g i))
    (hd : ∀ σ x i j, i ≠ j → ψ i σ x = 0 ∨ ψ j σ x = 0)
    (hdg : ∀ σ k a x i j, i ≠ j → g i σ k a x = 0 ∨ g j σ k a x = 0) :
    energy Z (sumWavefunction c ψ) (sumGradient c g) = ∑ i, (c i)^2 * energy Z (ψ i) (g i) := by
  have hk (σ : Spins n) (k : Fin n) (a : Fin 3) :
      (∫ x, ‖sumGradient c g σ k a x‖^2) =
        ∑ i, (c i)^2 * ∫ x, ‖g i σ k a x‖^2 := by
    simp only [sumGradient]
    simp_rw [norm_sq_sum_real_smul_of_disjoint c _ (hdg _ _ _ _)]
    rw [integral_finsetSum _ (fun i _ => ((h i).2.2.1 σ k a).norm.integrable_sq.const_mul ((c i)^2))]
    simp only [integral_const_mul]
  have hv (σ : Spins n) :
      (∫ x, coulombPotential Z x * ‖sumWavefunction c ψ σ x‖^2) =
        ∑ i, (c i)^2 * ∫ x, coulombPotential Z x * ‖ψ i σ x‖^2 := by
    simp only [sumWavefunction]
    simp_rw [norm_sq_sum_real_smul_of_disjoint c _ (hd _ _), Finset.mul_sum]
    simp_rw [← mul_assoc, mul_comm (coulombPotential Z _) ((c _)^2), mul_assoc]
    rw [integral_finsetSum _ (fun i _ => ((h i).integrable_potential Z σ).const_mul ((c i)^2))]
    simp only [integral_const_mul]
  unfold energy
  simp_rw [hk, hv]
  have hs : (∑ σ : Spins n, ∑ k : Fin n, ∑ a : Fin 3, ∑ i, (c i)^2 * ∫ x, ‖g i σ k a x‖^2) =
      ∑ i, (c i)^2 * ∑ σ : Spins n, ∑ k : Fin n, ∑ a : Fin 3, ∫ x, ‖g i σ k a x‖^2 := by
    simp_rw [Finset.sum_comm (f := fun a i => (c i)^2 * ∫ x, ‖g i _ _ a x‖^2)]
    simp_rw [Finset.sum_comm (f := fun k i => ∑ a : Fin 3, (c i)^2 * ∫ x, ‖g i _ k a x‖^2)]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  rw [hs, Finset.sum_comm (f := fun σ i => (c i)^2 * ∫ x, coulombPotential Z x * ‖ψ i σ x‖^2)]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum]
  ring

 theorem insertionSupport_gradient {n : ℕ} {R : ℝ} {f : Position → ℝ}
    {ψ : Wavefunction n} {g : Gradient n} (hf : ∀ y, ‖y‖ ≤ R → f y = 0)
    (hdf : ∀ a y, ‖y‖ ≤ R → fderiv ℝ f y (EuclideanSpace.single a 1) = 0)
    (hψ : ∀ σ x, R < ‖x‖ → ψ σ x = 0)
    (hg : ∀ σ i a x, R < ‖x‖ → g σ i a x = 0) (i : Fin (n+1)) (a : Fin 3) :
    InsertionSupport R (fun σ x => insertGradient f ψ g σ i a x) := by
  cases i using Fin.cases with
  | zero => exact insertionSupport_tensor (hdf a) hψ
  | succ i => exact insertionSupport_tensor hf (fun σ x hx => hg σ i a x hx)

 theorem wedgeInsert_antisymmetric {n : ℕ} {ψ : Wavefunction n} (hψ : IsAntisymmetric ψ)
    (f : Position → ℝ) : IsAntisymmetric (wedgeInsert f ψ) := by
  intro p σ
  have hl := (antisymmetrize_insert_eq hψ f (σ ∘ p)).comp_tendsto
    (configurationPerm_preserving p).quasiMeasurePreserving.tendsto_ae
  filter_upwards [hl, antisymmetrize_insert_eq hψ f σ,
    antisymmetrize_antisymmetric (insertWavefunction f ψ) p σ] with x hx hy hz
  change antisymmetrize (insertWavefunction f ψ) (σ ∘ p) (x ∘ p) = _ at hx
  rw [hx, hy] at hz
  simp only [Complex.real_smul, Complex.ofReal_natCast] at hz
  have hc : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  apply mul_left_cancel₀ hc
  simpa only [Function.comp_apply, configurationPerm_apply,
    mul_left_comm ((Equiv.Perm.sign p : ℤ) : ℂ)] using hz

 theorem FormRegular.wedgeInsert {n : ℕ} {f : Position → ℝ} {ψ : Wavefunction n} {g : Gradient n}
    (hψ : IsAntisymmetric ψ) (h : FormRegular (insertWavefunction f ψ) (insertGradient f ψ g)) :
    FormDomain (wedgeInsert f ψ) (wedgeInsertGradient f ψ g) :=
  ⟨wedgeInsert_antisymmetric hψ f,
    FormRegular.finite_sum (fun i => permutationSign (Equiv.swap 0 i))
      (fun i => h.permute (Equiv.swap 0 i))⟩

 theorem normSquared_wedgeInsert {n : ℕ} {R : ℝ} {f : Position → ℝ}
    {ψ : Wavefunction n} (hψLp : ∀ σ, MemLp (ψ σ) 2 volume) (hfLp : MemLp f 2 volume)
    (hs : InsertionSupport R (insertWavefunction f ψ)) :
    normSquared (wedgeInsert f ψ) = (n+1 : ℝ) * normSquared (insertWavefunction f ψ) := by
  have hLp (i : Fin (n+1)) (σ : Spins (n+1)) :
      MemLp (permuteWavefunction (Equiv.swap 0 i) (insertWavefunction f ψ) σ) 2 volume :=
    (insertWavefunction_memLp hψLp hfLp _).comp_measurePreserving
      (configurationPerm_preserving (Equiv.swap 0 i))
  unfold wedgeInsert
  rw [normSquared_disjoint_sum _ hLp (fun σ x i j hij => hs.placements_disjoint hs σ x hij)]
  simp only [pow_two, permutationSign_sq, one_mul, normSquared_permute, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

 theorem energy_wedgeInsert {n : ℕ} (Z : ℕ) {R : ℝ} {f : Position → ℝ}
    {ψ : Wavefunction n} {g : Gradient n}
    (h : FormRegular (insertWavefunction f ψ) (insertGradient f ψ g))
    (hs : InsertionSupport R (insertWavefunction f ψ))
    (hsg : ∀ i a, InsertionSupport R (fun σ x => insertGradient f ψ g σ i a x)) :
    energy Z (wedgeInsert f ψ) (wedgeInsertGradient f ψ g) =
      (n+1 : ℝ) * energy Z (insertWavefunction f ψ) (insertGradient f ψ g) := by
  unfold wedgeInsert wedgeInsertGradient
  rw [energy_disjoint_sum Z _ (fun i => h.permute (Equiv.swap 0 i))
    (fun σ x i j hij => hs.placements_disjoint hs σ x hij)
    (fun σ k a x i j hij => (hsg ((Equiv.swap 0 i).symm k) a).placements_disjoint
      (hsg ((Equiv.swap 0 j).symm k) a) σ x hij)]
  simp only [pow_two, permutationSign_sq, one_mul, energy_permute, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

 theorem integrable_supported_weight {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {ψ : A → ℂ} (hψ : MemLp ψ 2 μ) {W : A → ℝ} (hW : Measurable W)
    {C : ℝ} (hb : ∀ x, ψ x ≠ 0 → |W x| ≤ C) :
    Integrable (fun x => W x * ‖ψ x‖^2) μ := by
  apply (hψ.norm.integrable_sq.const_mul C).mono'
    (hW.aestronglyMeasurable.mul (hψ.aestronglyMeasurable.norm.pow 2))
  apply Eventually.of_forall
  intro x
  by_cases hx : ψ x = 0
  · simp [hx]
  · change ‖W x * ‖ψ x‖^2‖ ≤ C * ‖ψ x‖^2
    simpa only [Real.norm_eq_abs, abs_mul, abs_pow, abs_norm] using
      mul_le_mul_of_nonneg_right (hb x hx) (sq_nonneg ‖ψ x‖)

 theorem integrable_weighted_tensor {n : ℕ} {f : Position → ℝ} (hf : MemLp f 2 volume)
    {ψ : Configuration n → ℂ} {W : Configuration n → ℝ}
    (hW : Integrable (fun x => W x * ‖ψ x‖^2)) :
    Integrable (fun x : Configuration (n+1) => W (fun i => x i.succ) *
      ‖f (x 0) • ψ (fun i => x i.succ)‖^2) := by
  have hi : Integrable (fun z : Position × Configuration n => (f z.1)^2 * (W z.2 * ‖ψ z.2‖^2)) :=
    hf.integrable_sq.mul_prod hW
  have hp := (configurationSplit_preserving n).integrable_comp_of_integrable hi
  apply hp.congr
  exact Eventually.of_forall fun x => by
    simp only [Function.comp_apply, configurationSplit_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring

 theorem integral_weighted_tensor {n : ℕ} (f : Position → ℝ)
    (ψ : Configuration n → ℂ) (W : Configuration n → ℝ) :
    (∫ x : Configuration (n+1), W (fun i => x i.succ) * ‖f (x 0) • ψ (fun i => x i.succ)‖^2) =
      (∫ y : Position, (f y)^2) * ∫ x : Configuration n, W x * ‖ψ x‖^2 := by
  have he := (configurationSplit_preserving n).integral_comp
    (configurationSplit n).toHomeomorph.measurableEmbedding
    (fun z : Position × Configuration n => (f z.1)^2 * (W z.2 * ‖ψ z.2‖^2))
  have hi := integral_prod_mul (μ := (volume : Measure Position)) (ν := (volume : Measure (Configuration n)))
    (fun y => (f y)^2) (fun x => W x * ‖ψ x‖^2)
  rw [← hi]
  change _ = ∫ z : Position × Configuration n, (f z.1)^2 * (W z.2 * ‖ψ z.2‖^2)
  rw [← he]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [configurationSplit_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring

 theorem inserted_nuclear_bound {n : ℕ} {d : ℝ} (hd : 0 < d)
    {f : Position → ℝ} {ψ : Wavefunction n} (hf : ∀ y, ‖y‖ ≤ d → f y = 0)
    (σ : Spins (n+1)) (x : Configuration (n+1)) (hx : insertWavefunction f ψ σ x ≠ 0) :
    |‖x 0‖⁻¹| ≤ d⁻¹ := by
  have hdf : d < ‖x 0‖ := by
    by_contra hh
    have hhf := hf (x 0) (le_of_not_gt hh)
    exact hx (by simp [insertWavefunction, hhf])
  simpa only [one_div, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] using
    one_div_le_one_div_of_le hd hdf.le

 theorem inserted_pair_bound {n : ℕ} {R d : ℝ} (hRd : R < d)
    {f : Position → ℝ} {ψ : Wavefunction n} (hf : ∀ y, ‖y‖ ≤ d → f y = 0)
    (hψ : ∀ σ x, R < ‖x‖ → ψ σ x = 0)
    (σ : Spins (n+1)) (x : Configuration (n+1)) (i : Fin n)
    (hx : insertWavefunction f ψ σ x ≠ 0) : |‖x 0-x i.succ‖⁻¹| ≤ (d-R)⁻¹ := by
  have hdf : d < ‖x 0‖ := by
    by_contra hh
    exact hx (by simp [insertWavefunction, hf (x 0) (le_of_not_gt hh)])
  have htail := (insertionSupport_tensor (fun y hy => hf y (hy.trans hRd.le)) hψ σ x hx).2 i
  have hb := norm_sub_norm_le (x 0) (x i.succ)
  have hdist : d-R ≤ ‖x 0-x i.succ‖ := by linarith
  simpa only [one_div, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] using
    one_div_le_one_div_of_le (sub_pos.mpr hRd) hdist

 theorem FormRegular.insert_separated {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (h : FormRegular ψ g) {R d : ℝ} (hd : 0 < d) (hRd : R < d)
    (hψ : ∀ σ x, R < ‖x‖ → ψ σ x = 0)
    {f : Position → ℝ} (hf : ContDiff ℝ ∞ f) (hfLp : MemLp f 2 volume)
    (hdfLp : ∀ a, MemLp (fun y => fderiv ℝ f y (EuclideanSpace.single a 1)) 2 volume)
    (hfout : ∀ y, ‖y‖ ≤ d → f y = 0) :
    FormRegular (insertWavefunction f ψ) (insertGradient f ψ g) := by
  refine ⟨HasWeakGradient.insert h.1 h.2.1 h.2.2.1 hf hfLp hdfLp,
    insertWavefunction_memLp h.2.1 hfLp, insertGradient_memLp h.2.1 h.2.2.1 hfLp hdfLp, ?_, ?_⟩
  · intro σ i
    cases i using Fin.cases with
    | zero =>
      exact integrable_supported_weight (insertWavefunction_memLp h.2.1 hfLp σ)
        (by fun_prop) (inserted_nuclear_bound hd hfout σ)
    | succ i =>
      by_cases hσ : σ 0 = 0
      · simpa only [insertWavefunction, hσ, ↓reduceIte] using
          integrable_weighted_tensor hfLp (h.2.2.2.1 (fun i => σ i.succ) i)
      · simp [insertWavefunction, hσ]
  · intro σ i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (lt_irrefl _ hij).elim
      | succ j =>
        exact integrable_supported_weight (insertWavefunction_memLp h.2.1 hfLp σ)
          (by fun_prop) (inserted_pair_bound hRd hfout hψ σ · j)
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (not_lt_of_ge (Fin.zero_le _) hij).elim
      | succ j =>
        by_cases hσ : σ 0 = 0
        · simpa only [insertWavefunction, hσ, ↓reduceIte] using
            integrable_weighted_tensor hfLp (h.pair (fun i => σ i.succ) i j)
        · simp [insertWavefunction, hσ]

 theorem coulombPotential_cons {n : ℕ} (Z : ℕ) (y : Position) (x : Configuration n) :
    coulombPotential Z (Fin.cons y x) = coulombPotential Z x - (Z : ℝ)*‖y‖⁻¹ +
      ∑ i : Fin n, ‖y-x i‖⁻¹ := by
  have hs {k : ℕ} (z : Configuration k) :
      (∑ i : Fin k, ∑ j ∈ Finset.univ.filter (fun j => i < j), ‖z i-z j‖⁻¹) =
      (1/2:ℝ) * ∑ i : Fin k, ∑ j : Fin k, ‖z i-z j‖⁻¹ :=
    half_ordered_sum _ (fun i j => by rw [norm_sub_rev]) (fun i => by simp)
  simp only [coulombPotential, hs, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    sub_self, norm_zero, inv_zero, zero_add, Finset.sum_add_distrib]
  simp_rw [norm_sub_rev _ y]
  ring

 theorem gradientNormSquared_eq {n : ℕ} (g : Gradient n) :
    gradientNormSquared g = ∑ σ : Spins n, ∑ i : Fin n, ∑ a : Fin 3, ∫ x, ‖g σ i a x‖^2 := by
  unfold gradientNormSquared normSquared
  simp_rw [Finset.sum_comm (f := fun a σ => ∫ x, ‖g σ _ a x‖^2)]
  rw [Finset.sum_comm]

 theorem energy_decompose {n : ℕ} (Z : ℕ) (ψ : Wavefunction n) (g : Gradient n) :
    energy Z ψ g = (1/2 : ℝ)*gradientNormSquared g + potentialForm Z ψ := by
  rw [gradientNormSquared_eq]
  rfl

end NeutralAtom
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_ParticleGradientNorm
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

 theorem gradientNormSquared_insert {n : ℕ} (f : Position → ℝ)
    (ψ : Wavefunction n) (g : Gradient n) :
    gradientNormSquared (insertGradient f ψ g) =
      (∫ y : Position, (f y)^2) * gradientNormSquared g + oneParticleGradientNorm f * normSquared ψ := by
  unfold gradientNormSquared
  rw [Fin.sum_univ_succ]
  change (∑ a : Fin 3, normSquared (insertWavefunction (fun y => fderiv ℝ f y (EuclideanSpace.single a 1)) ψ)) +
      (∑ i : Fin n, ∑ a : Fin 3, normSquared (insertWavefunction f (fun σ x => g σ i a x))) = _
  simp only [normSquared_insert, oneParticleGradientNorm, Finset.sum_mul, Finset.mul_sum]
  ring

 theorem weighted_normSquared_insert {n : ℕ} (f : Position → ℝ) (ψ : Wavefunction n)
    (W : Configuration n → ℝ) :
    (∑ σ : Spins (n+1), ∫ x : Configuration (n+1),
      W (fun i => x i.succ)*‖insertWavefunction f ψ σ x‖^2) =
      (∫ y : Position, (f y)^2) * ∑ σ : Spins n, ∫ x : Configuration n, W x*‖ψ σ x‖^2 := by
  classical
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => Fin 2))]
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, insertWavefunction, Fin.cons_zero,
    Fin.cons_succ, h10, ↓reduceIte]
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, integral_zero,
    Finset.sum_const_zero, add_zero, integral_weighted_tensor, Finset.mul_sum]

 theorem potentialForm_insert_le {n : ℕ} (Z : ℕ) {ψ : Wavefunction n} {g : Gradient n}
    (h : FormRegular ψ g) {R d : ℝ} (hRd : R < d)
    (hψ : ∀ σ x, R < ‖x‖ → ψ σ x = 0)
    {f : Position → ℝ} (hfLp : MemLp f 2 volume)
    (hfout : ∀ y, ‖y‖ ≤ d → f y = 0)
    (hi : FormRegular (insertWavefunction f ψ) (insertGradient f ψ g)) :
    potentialForm Z (insertWavefunction f ψ) ≤
      (∫ y : Position, (f y)^2) * potentialForm Z ψ +
        ((n : ℝ)*(d-R)⁻¹)*normSquared (insertWavefunction f ψ) := by
  let C : ℝ := (n : ℝ)*(d-R)⁻¹
  have hold (σ : Spins (n+1)) : Integrable (fun x : Configuration (n+1) =>
      coulombPotential Z (fun i => x i.succ)*‖insertWavefunction f ψ σ x‖^2) := by
    by_cases hσ : σ 0 = 0
    · simpa only [insertWavefunction, hσ, ↓reduceIte] using
        integrable_weighted_tensor hfLp (h.integrable_potential Z (fun i => σ i.succ))
    · simp [insertWavefunction, hσ]
  have hnew (σ : Spins (n+1)) := ((hi.2.1 σ).norm.integrable_sq).const_mul C
  have hb (σ : Spins (n+1)) (x : Configuration (n+1)) :
      coulombPotential Z x*‖insertWavefunction f ψ σ x‖^2 ≤
        coulombPotential Z (fun i => x i.succ)*‖insertWavefunction f ψ σ x‖^2 +
          C*‖insertWavefunction f ψ σ x‖^2 := by
    by_cases hx : insertWavefunction f ψ σ x = 0
    · simp [hx]
    · have he : x = Fin.cons (x 0) (fun i => x i.succ) := by ext i; cases i using Fin.cases <;> rfl
      have hsum : (∑ i : Fin n, ‖x 0-x i.succ‖⁻¹) ≤ C := by
        calc
          _ ≤ ∑ _i : Fin n, (d-R)⁻¹ := Finset.sum_le_sum fun i _ =>
            (le_abs_self _).trans (inserted_pair_bound hRd hfout hψ σ x i hx)
          _ = C := by simp [C]
      have hpot : coulombPotential Z x ≤ coulombPotential Z (fun i => x i.succ) + C := by
        conv_lhs => rw [he, coulombPotential_cons]
        have hn : 0 ≤ (Z : ℝ)*‖x 0‖⁻¹ := by positivity
        linarith
      simpa only [add_mul] using mul_le_mul_of_nonneg_right hpot (sq_nonneg ‖insertWavefunction f ψ σ x‖)
  have hiσ (σ : Spins (n+1)) :
      (∫ x, coulombPotential Z x*‖insertWavefunction f ψ σ x‖^2) ≤
        (∫ x, coulombPotential Z (fun i => x i.succ)*‖insertWavefunction f ψ σ x‖^2) +
          C*(∫ x, ‖insertWavefunction f ψ σ x‖^2) := by
    have hm := integral_mono (hi.integrable_potential Z σ) ((hold σ).add (hnew σ)) (hb σ)
    change _ ≤ ∫ x, coulombPotential Z (fun i => x i.succ)*‖insertWavefunction f ψ σ x‖^2 +
      C*‖insertWavefunction f ψ σ x‖^2 at hm
    rw [integral_add (hold σ) (hnew σ), integral_const_mul] at hm
    exact hm
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun σ _ => hiσ σ)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [weighted_normSquared_insert] at hsum
  exact hsum

 theorem energy_insert_le {n : ℕ} (Z : ℕ) {ψ : Wavefunction n} {g : Gradient n}
    (h : FormRegular ψ g) (hn : normSquared ψ = 1) {R d : ℝ} (hRd : R < d)
    (hψ : ∀ σ x, R < ‖x‖ → ψ σ x = 0)
    {f : Position → ℝ} (hfLp : MemLp f 2 volume) (hfn : (∫ y : Position, (f y)^2) = 1)
    (hfout : ∀ y, ‖y‖ ≤ d → f y = 0)
    (hi : FormRegular (insertWavefunction f ψ) (insertGradient f ψ g)) :
    energy Z (insertWavefunction f ψ) (insertGradient f ψ g) ≤ energy Z ψ g +
      (1/2 : ℝ)*oneParticleGradientNorm f + (n : ℝ)*(d-R)⁻¹ := by
  have hp := potentialForm_insert_le Z h hRd hψ hfLp hfout hi
  simp only [hfn, normSquared_insert, hn, one_mul, mul_one] at hp
  rw [energy_decompose, energy_decompose, gradientNormSquared_insert, hfn, hn, one_mul, mul_one]
  linarith

theorem distantCenter_norm : ‖distantCenter‖ = 4 := by
  simp [distantCenter, norm_smul, EuclideanSpace.single, PiLp.norm_single]

theorem bindingBump_smooth : ContDiff ℝ ∞ (fun y : Position => bindingBump y) := bindingBump.contDiff

theorem distantMass_pos : 0 < distantMass := by
  have hc : Continuous (fun y : Position => (bindingBump y)^2) :=
    bindingBump_smooth.continuous.pow 2
  have hs : HasCompactSupport (fun y : Position => (bindingBump y)^2) := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : Position) 2)
    intro y hy
    have hh : 2 ≤ ‖y‖ := (lt_of_not_ge (by simpa [Metric.mem_closedBall, dist_zero_right] using hy)).le
    rw [bindingBump.zero_of_le_dist (by simpa [bindingBump] using hh)]
    norm_num
  apply integral_pos_of_integrable_nonneg_nonzero hc (hc.integrable_of_hasCompactSupport hs)
    (fun y => sq_nonneg _) (x := 0)
  rw [bindingBump.one_of_mem_closedBall (by simp [bindingBump])]
  norm_num

theorem distantPacket_smooth (t : ℝ) : ContDiff ℝ ∞ (distantPacket t) :=
  contDiff_const.mul (bindingBump.contDiff.comp
    (((contDiff_const (c := t⁻¹)).smul (contDiff_id (E := Position))).sub contDiff_const))

theorem distantPacket_compact {t : ℝ} (ht : 0 < t) : HasCompactSupport (distantPacket t) := by
  let u : ℝˣ := Units.mk0 t⁻¹ (inv_ne_zero ht.ne')
  have hc : HasCompactSupport (fun y : Position => bindingBump (t⁻¹ • y - distantCenter)) :=
    (bindingBump.hasCompactSupport.comp_homeomorph (Homeomorph.subRight distantCenter)).comp_homeomorph
      (Homeomorph.smul u)
  exact hc.mul_left

theorem distantPacket_memLp {t : ℝ} (ht : 0 < t) : MemLp (distantPacket t) 2 volume :=
  (distantPacket_smooth t).continuous.memLp_of_hasCompactSupport (distantPacket_compact ht)

theorem distantPacket_derivative_memLp {t : ℝ} (ht : 0 < t) (v : Position) :
    MemLp (fun y => fderiv ℝ (distantPacket t) y v) 2 volume :=
  (((distantPacket_smooth t).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
    ((distantPacket_compact ht).fderiv_apply ℝ v)

theorem integral_distant_comp {t : ℝ} (ht : 0 < t) (F : Position → ℝ) :
    (∫ y : Position, F (t⁻¹ • y - distantCenter)) = t^3 * ∫ y : Position, F y := by
  rw [show (fun y : Position => F (t⁻¹ • y-distantCenter)) =
      (fun y : Position => (fun z : Position => F (z-distantCenter)) (t⁻¹ • y)) from rfl]
  rw [Measure.integral_comp_smul_of_nonneg volume (fun z : Position => F (z-distantCenter)) t⁻¹ (hR := by positivity)]
  simp [integral_sub_right_eq_self, Position, inv_pow]

theorem distantPacket_normalized {t : ℝ} (ht : 0 < t) :
    (∫ y : Position, (distantPacket t y)^2) = 1 := by
  simp only [distantPacket, mul_pow, integral_const_mul]
  rw [integral_distant_comp ht (fun y => (bindingBump y)^2)]
  rw [inv_pow, Real.sq_sqrt (mul_nonneg (pow_nonneg ht.le 3) distantMass_pos.le)]
  change (t^3*distantMass)⁻¹*(t^3*distantMass) = 1
  exact inv_mul_cancel₀ (mul_ne_zero (pow_ne_zero _ ht.ne') distantMass_pos.ne')

theorem distantPacket_zero {t : ℝ} (ht : 0 < t) {y : Position} (hy : ‖y‖ ≤ 2*t) :
    distantPacket t y = 0 := by
  have hnorm : ‖t⁻¹ • y‖ ≤ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    exact (inv_mul_le_iff₀ ht).mpr (by nlinarith)
  have hdist : 2 ≤ ‖t⁻¹ • y - distantCenter‖ := by
    have h := norm_sub_norm_le distantCenter (t⁻¹ • y)
    rw [distantCenter_norm, norm_sub_rev] at h
    linarith
  have := bindingBump.zero_of_le_dist (by simpa [bindingBump] using hdist)
  simp [distantPacket, this]

theorem distantPacket_derivative_zero {t : ℝ} (ht : 0 < t) {y : Position}
    (hy : ‖y‖ ≤ t) (v : Position) : fderiv ℝ (distantPacket t) y v = 0 := by
  have he : distantPacket t =ᶠ[𝓝 y] (fun _ => 0) := by
    have hn : ‖y‖ < 2*t := by linarith
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hn] with z hz
    exact distantPacket_zero ht hz.le
  rw [he.fderiv_eq]
  simp

theorem distantPacket_fderiv {t : ℝ} (y v : Position) :
    fderiv ℝ (distantPacket t) y v =
      (Real.sqrt (t^3*distantMass))⁻¹ * t⁻¹ *
        fderiv ℝ (fun z : Position => bindingBump z) (t⁻¹ • y-distantCenter) v := by
  have hb := (bindingBump_smooth.differentiable (by simp) (t⁻¹ • y-distantCenter)).hasFDerivAt
  have hc := ((hasFDerivAt_id (𝕜 := ℝ) y).const_smul t⁻¹).sub_const distantCenter
  have hh := ((hb.comp y hc).const_mul (Real.sqrt (t^3*distantMass))⁻¹).fderiv
  change fderiv ℝ (fun y : Position => (Real.sqrt (t^3*distantMass))⁻¹ *
    bindingBump (t⁻¹ • y-distantCenter)) y v = _
  change fderiv ℝ (fun y : Position => (Real.sqrt (t^3*distantMass))⁻¹ *
    (bindingBump ∘ fun x : Position => (t⁻¹ • id) x - distantCenter) y) y v = _
  rw [hh]
  simp [mul_assoc]

theorem distantPacket_gradientNorm {t : ℝ} (ht : 0 < t) :
    oneParticleGradientNorm (distantPacket t) =
      t⁻¹^2 * (distantMass⁻¹ * oneParticleGradientNorm bindingBump) := by
  unfold oneParticleGradientNorm
  simp_rw [distantPacket_fderiv, mul_pow, integral_const_mul]
  have hi (a : Fin 3) := integral_distant_comp ht
    (fun y => (fderiv ℝ (fun z : Position => bindingBump z) y (EuclideanSpace.single a 1))^2)
  simp_rw [hi]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [inv_pow, Real.sq_sqrt (mul_nonneg (pow_nonneg ht.le 3) distantMass_pos.le)]
  field_simp

theorem distantInsertion_error_tendsto (n : ℕ) (R : ℝ) :
    Tendsto (fun t : ℝ => (1/2 : ℝ) * (t⁻¹^2 *
      (distantMass⁻¹ * oneParticleGradientNorm bindingBump)) + (n : ℝ)*(t-R)⁻¹)
      atTop (𝓝 0) := by
  have hi : Tendsto (fun t : ℝ => (t-R)⁻¹) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp
      (by simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-R) tendsto_id)
  have hh := ((tendsto_inv_atTop_zero.pow 2).mul_const
    (distantMass⁻¹ * oneParticleGradientNorm bindingBump)).const_mul (1/2 : ℝ)
  simpa using hh.add (hi.const_mul (n : ℝ))

theorem FormDomain.exists_inserted_trial {n : ℕ} (Z : ℕ)
    {ψ : Wavefunction n} {g : Gradient n} (hd : FormDomain ψ g)
    (hn : normSquared ψ = 1) {R : ℝ}
    (hψ : ∀ σ x, R < ‖x‖ → ψ σ x = 0)
    (hg : ∀ σ i a x, R < ‖x‖ → g σ i a x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (χ : Wavefunction (n+1)) (h : Gradient (n+1)),
      FormDomain χ h ∧ normSquared χ = 1 ∧ energy Z χ h < energy Z ψ g + ε := by
  have he : ∀ᶠ t : ℝ in atTop, (1/2 : ℝ) *
      (t⁻¹^2 * (distantMass⁻¹ * oneParticleGradientNorm bindingBump)) + (n : ℝ)*(t-R)⁻¹ < ε :=
    (distantInsertion_error_tendsto n R).eventually (Iio_mem_nhds hε)
  obtain ⟨t, ht, htR, hterr⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    ((eventually_gt_atTop R).and he)).exists
  let f := distantPacket t
  have hfLp : MemLp f 2 volume := distantPacket_memLp ht
  have hfn : (∫ y : Position, (f y)^2) = 1 := distantPacket_normalized ht
  have hfout : ∀ y, ‖y‖ ≤ t → f y = 0 :=
    fun y hy => distantPacket_zero ht (by linarith)
  have hi : FormRegular (insertWavefunction f ψ) (insertGradient f ψ g) :=
    FormRegular.insert_separated hd.2 ht htR hψ (distantPacket_smooth t) hfLp
      (fun a => distantPacket_derivative_memLp ht _) hfout
  have hfs : ∀ y, ‖y‖ ≤ R → f y = 0 := fun y hy => hfout y (hy.trans htR.le)
  have hs := insertionSupport_tensor hfs hψ
  have hgs : ∀ i a, InsertionSupport R (fun σ x => insertGradient f ψ g σ i a x) :=
    insertionSupport_gradient hfs
      (fun a y hy => distantPacket_derivative_zero ht (hy.trans htR.le) _) hψ hg
  let c : ℝ := (Real.sqrt (n+1 : ℝ))⁻¹
  have hc : c^2 * (n+1 : ℝ) = 1 := by
    dsimp [c]
    rw [inv_pow, Real.sq_sqrt (by positivity), inv_mul_cancel₀ (by positivity)]
  refine ⟨scaleWavefunction c (wedgeInsert f ψ), scaleGradient c (wedgeInsertGradient f ψ g),
    (hi.wedgeInsert hd.1).scale c, ?_, ?_⟩
  · rw [normSquared_scale, normSquared_wedgeInsert hd.2.2.1 hfLp hs,
      normSquared_insert, hfn, hn]
    simpa only [one_mul, mul_one] using hc
  · rw [energy_scale, energy_wedgeInsert Z hi hs hgs, ← mul_assoc, hc, one_mul]
    have hh := energy_insert_le Z hd.2 hn htR hψ hfLp hfn hfout hi
    rw [distantPacket_gradientNorm ht] at hh
    linarith

theorem FormDomain.exists_successor_trial {n : ℕ} (Z : ℕ)
    {ψ : Wavefunction n} {g : Gradient n} (hd : FormDomain ψ g)
    (hn : normSquared ψ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ (χ : Wavefunction (n+1)) (h : Gradient (n+1)),
      FormDomain χ h ∧ normSquared χ = 1 ∧ energy Z χ h < energy Z ψ g + ε := by
  obtain ⟨R, χ, h, _, hχ, hχn, hχe, hχs, hhs⟩ := hd.exists_compact_approximation Z hn
    (half_pos hε)
  obtain ⟨χ', h', hχ', hχ'n, hχ'e⟩ := hχ.exists_inserted_trial Z hχn hχs hhs (half_pos hε)
  exact ⟨χ', h', hχ', hχ'n, by linarith⟩

theorem sectorEnergy_le_trial {Z n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hψ : FormDomain ψ g) (hn : normSquared ψ = 1) :
    sectorEnergy Z n ≤ (energy Z ψ g : EReal) := sInf_le ⟨ψ, g, hψ, hn, rfl⟩

theorem sectorEnergy_succ_le (Z n : ℕ) : sectorEnergy Z (n+1) ≤ sectorEnergy Z n := by
  apply le_sInf
  rintro e ⟨ψ, g, hd, hn, rfl⟩
  by_contra hh
  obtain ⟨r, hEr, hrE⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hh)
  have hε : 0 < r-energy Z ψ g := sub_pos.mpr (EReal.coe_lt_coe_iff.mp hEr)
  obtain ⟨χ, h, hχ, hχn, hχe⟩ := hd.exists_successor_trial Z hn hε
  have hlt : energy Z χ h < r := by linarith
  have hle := sectorEnergy_le_trial (Z := Z) hχ hχn
  exact (not_lt_of_ge hle) ((EReal.coe_lt_coe_iff.mpr hlt).trans hrE)

theorem sectorEnergy_antitone (Z : ℕ) : Antitone (sectorEnergy Z) :=
  antitone_nat_of_succ_le (sectorEnergy_succ_le Z)

theorem vacuum_volume_univ : (volume : Measure (Configuration 0)) Set.univ = 1 := by
  rw [volume_pi, Measure.pi_univ]
  simp

theorem vacuum_formDomain : FormDomain vacuumWavefunction vacuumGradient := by
  let : IsProbabilityMeasure (volume : Measure (Configuration 0)) := ⟨vacuum_volume_univ⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p σ
    have hp : p = 1 := Subsingleton.elim _ _
    simp [vacuumWavefunction, hp]
  · intro σ i
    exact Fin.elim0 i
  · intro σ
    exact memLp_const _
  · intro σ i
    exact Fin.elim0 i
  · intro σ i
    exact Fin.elim0 i
  · intro σ i
    exact Fin.elim0 i

theorem vacuum_normalized : normSquared vacuumWavefunction = 1 := by
  let : IsProbabilityMeasure (volume : Measure (Configuration 0)) := ⟨vacuum_volume_univ⟩
  simp [normSquared, vacuumWavefunction, Spins]

theorem energy_vacuum_sector (Z : ℕ) (ψ : Wavefunction 0) (g : Gradient 0) : energy Z ψ g = 0 := by
  simp [energy, coulombPotential]

theorem sectorEnergy_vacuum (Z : ℕ) : sectorEnergy Z 0 = 0 := by
  apply le_antisymm
  · simpa [energy_vacuum_sector] using
      sectorEnergy_le_trial (Z := Z) vacuum_formDomain vacuum_normalized
  · apply le_sInf
    rintro e ⟨ψ, g, _, _, rfl⟩
    simp [energy_vacuum_sector]

theorem sectorEnergy_nonpos (Z n : ℕ) : sectorEnergy Z n ≤ 0 := by
  simpa [sectorEnergy_vacuum] using sectorEnergy_antitone Z (Nat.zero_le n)

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_SpectralTheory_SectorBottomBridge
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
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

theorem sectorEnergy_eq_formBottom (Z : ℕ) (hZ : 1≤Z) (n : ℕ) :
    sectorEnergy Z n=Coulomb.sectorFormBottom (Coulomb.atom Z hZ) n := by
  apply le_antisymm
  · apply le_sInf
    rintro e ⟨u,ha,hm,rfl⟩
    have H := sectorEnergy_le_trial (Z:=Z) (fromH1_domain u ha) ((fromH1_mass u).trans hm)
    rwa [fromH1_energy Z hZ] at H
  · apply le_sInf
    rintro e ⟨ψ,g,hd,hn,rfl⟩
    let u := asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1
    have H : Coulomb.sectorFormBottom (Coulomb.atom Z hZ) n≤
        (Coulomb.form (Coulomb.atom Z hZ) u:EReal) :=
      sInf_le ⟨u,asH1_antisymmetric hd,(asH1_mass ..).trans hn,rfl⟩
    rwa [asH1_energy Z hZ] at H

end NeutralAtom

end
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_AtomicGlobalScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace Coulomb

lemma atom_unrestricted_bottom_nonpos (Z : ℕ) (hZ : 1≤Z) :
    unrestrictedFormBottom (atom Z hZ)≤0 := by
  apply (iInf_le (fun n => sectorFormBottom (atom Z hZ) n) 0).trans
  rw [←NeutralAtom.sectorEnergy_eq_formBottom Z hZ]
  exact NeutralAtom.sectorEnergy_nonpos Z 0
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PhysicalInitialPoint
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

theorem physical_initial_potential_point : ∃ C : ℝ,0<C ∧
    ∀ {N J : ℕ} (Z : ℕ) (hZ : 1≤Z) {ψ : Wavefunction (N+1)} {g : Gradient (N+1)},
    ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
    (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)),FormDomain χ h → normSquared χ=1 →
      energy Z ψ g≤energy Z χ h) →
    ∀ {E D : ℝ},(E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g≤E+D → (N+1:ℝ)≤3*(Z:ℝ) →
    ∀ (g₀ : 𝓢(Position,ℝ)),(∫ w,g₀ w^2)=1 →
    (∀ w,g₀ w=g₀ (EuclideanSpace.single 0 ‖w‖)) → (∀ w,1<‖w‖ → g₀ w=0) →
    ∀ {c r₀ s : ℝ},0 < c → 0 < r₀ → 0 < s → c*(1+packetExponent)*s^packetExponent≤1/2 →
    retainedInverseOffset D r₀≤(Z:ℝ)^(7/3:ℝ) → ∀ y : Position,
    letI := rawLaw_isProbability hd.2.2.1 hn
    let P := observationLaw J (rawLaw ψ)
    let r := fun k : Fin J => r₀*2^k.val
    P.real {a | C*(Z:ℝ)^(4/3:ℝ)≤potentialOf
      (conditionalPacketDensity P Prod.fst (tailObservation r 0) g₀ c r₀ s (tailObservation r 0 a)) y} ≤ r₀^42 := by
  obtain ⟨C,hC,HC⟩ := atomic_global_master_potential
  refine ⟨2*C,by positivity,?_⟩
  intro N J Z hZ ψ g hd hn hmin E D hE hbase hnum g₀ hm hrad hg c r₀ s hc hr₀ hs hq hoff y
  have := rawLaw_isProbability hd.2.2.1 hn
  dsimp only
  let P := observationLaw J (rawLaw ψ)
  let r : Fin J → ℝ := fun k => r₀*2^k.val
  let V := fun datum : Fin J → UnorderedArray (N+1) =>
    potentialOf (conditionalPacketDensity P Prod.fst (tailObservation r 0) g₀ c r₀ s datum) y
  let B : Set (Fin J → UnorderedArray (N+1)) := {datum | 2*C*(Z:ℝ)^(4/3:ℝ)≤V datum}
  have hgs : HasCompactSupport (g₀ : Position → ℝ) := HasCompactSupport.intro
    (isCompact_closedBall (0:Position) 1) (fun z hz => hg z
      (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz))
  have hV : Measurable V := measurable_conditionalPacketPotential_data P Prod.fst
    (tailObservation r 0) g₀.continuous hgs hm hc hr₀ hs y
  have hB : MeasurableSet B := measurableSet_le measurable_const hV
  change P.real (tailObservation r 0 ⁻¹' B) ≤ r₀^42
  by_contra H
  have hp : r₀^42<P.real (tailObservation r 0 ⁻¹' B) := lt_of_not_ge H
  have hp0 : 0<P.real (tailObservation r 0 ⁻¹' B) := (pow_pos hr₀ 42).trans hp
  have hp1 : P.real (tailObservation r 0 ⁻¹' B)≤1 := measureReal_le_one
  have hr (k : Fin J) : 0 < r k := by dsimp [r]; positivity
  have hpEq := physical_retainedTailEvent_probability hd.2.2.1 hn r hr 0 hB
  obtain ⟨u,hu,hum,hue,hlaw⟩ := atomic_arrayEvent_state Z hZ hd hn hmin hbase
    (fun k : RetainedScales J 0 => (r₀*2^k.val.val)^(101/100:ℝ))
    (fun k => Real.rpow_pos_of_pos (by positivity) _)
    (hB.preimage (measurable_retainedTailObservation 0))
    (fun p z => by simp only [mem_preimage,retainedTailObservation_permute])
    (hpEq ▸ hp0)
  have hoff' := retained_event_offset_le (D:=D) hr₀ J 0
    (by simpa only [pow_zero,mul_one] using hp.le) hp1
  have hEn : E≤0 := EReal.coe_le_coe_iff.mp (hE.trans (Coulomb.atom_unrestricted_bottom_nonpos Z hZ))
  have hue' : Coulomb.form (Coulomb.atom Z hZ) u≤(Z:ℝ)^(7/3:ℝ) := by
    rw [←hpEq] at hue
    simp only [pow_zero,mul_one] at hoff'
    linarith only [hue,hoff',hoff,hEn]
  have Hupper := HC Z hZ u hu hum hnum hue' g₀ hm hrad hg hc hr₀ hs hq y
  have Hmean := retainedEvent_potential_mean hd.2.2.1 hn r hr 0 hB u hum hlaw
    g₀.continuous hgs hm hc hr₀ hs y
  have Hlower := le_normalized_event (hB.preimage (measurable_tailObservation r 0))
    (conditionalPacketPotential_integrable P (rawLaw ψ) (observationLaw_rawProjection _)
      (measurable_tailObservation r 0) g₀.continuous hgs hm hc hr₀ hs y) hp0
    (Eventually.of_forall (fun a (ha : a∈tailObservation r 0 ⁻¹' B) => ha))
  rw [←Hmean] at Hlower
  have hz : 0<(Z:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0<1) hZ)
  have hcpos : 0<C*(Z:ℝ)^(4/3:ℝ) := mul_pos hC (Real.rpow_pos_of_pos hz _)
  nlinarith only [Hupper,Hlower,hcpos]
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology Classical SchwartzMap
noncomputable section
namespace NeutralAtom

lemma mixturePacketDensity_explicit_bound {n : ℕ} {g : Position → ℝ}
    (hg : Continuous g) (hgs : HasCompactSupport g) {A c r s : ℝ}
    (hA : 0≤A) (hAb : ∀ x,g x^2≤A) (hc : 0 < c) (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s)
    (ν : Measure (Configuration n)) [IsProbabilityMeasure ν] (y : Position) :
    mixturePacketDensity ν g c r s y≤(n:ℝ)*((c*r*r^packetExponent)^(-3:ℤ)*A) := by
  have H := integral_mono (rawPacketDensity_integrable_configuration hg hgs hc hr hs ν y)
    (integrable_const ((n:ℝ)*((c*r*r^packetExponent)^(-3:ℤ)*A)))
    (fun x => by simpa only [min_eq_left hrs] using rawPacketDensity_bound hA hAb hc hr hs x y)
  simpa only [mixturePacketDensity,integral_const,probReal_univ,one_smul] using H

lemma initial_width_modulus_identity {c r : ℝ} (_ : 0 < c) (hr : 0 < r) :
    (c*r*r^packetExponent)^(-3:ℤ)*r^4=(c^3)⁻¹*r^(1-3*packetExponent) := by
  have hwidth : c*r*r^packetExponent=c*r^(1+packetExponent) := by
    rw [Real.rpow_add hr,Real.rpow_one]; ring
  rw [hwidth,zpow_neg,zpow_ofNat,mul_pow,←Real.rpow_mul_natCast hr.le]
  calc
    _=(c^3)⁻¹*(r^4/r^((1+packetExponent)*3)) := by
      simp only [mul_inv_rev,div_eq_mul_inv]
      ring_nf
    _=_ := by
      rw [←Real.rpow_natCast r 4,←Real.rpow_sub hr]
      congr 2
      ring

lemma initialPacketModulus_tendsto (A c : ℝ) :
    Tendsto (initialPacketModulus A c) (𝓝[>] 0) (𝓝 0) := by
  have H := (((tendsto_positive_rpow_zero (by norm_num [packetExponent] :
    (0:ℝ)<1-3*packetExponent)).const_mul (A*(c^3)⁻¹)).add
    ((tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0)).pow 4)).const_mul 3
  convert H using 1 <;> simp only [mul_zero,zero_pow (by decide : 4≠0),add_zero,id_eq]
  funext r
  rfl

theorem initial_potential_mesh_modulus {n : ℕ} {g : Position → ℝ}
    (hg : Continuous g) (hgs : HasCompactSupport g) (hm : (∫ x,g x^2)=1)
    {A c r s Z : ℝ} (hA : 0≤A) (hAb : ∀ x,g x^2≤A)
    (hc : 0 < c) (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s) (_ : 0≤Z) (hn : (n:ℝ)≤3*Z)
    (ν : Measure (Configuration n)) [IsProbabilityMeasure ν]
    {x y : Position} (hxy : ‖x-y‖ ≤ r^3) :
    |potentialOf (mixturePacketDensity ν g c r s) x-potentialOf (mixturePacketDensity ν g c r s) y|≤
      (Z/r)*initialPacketModulus (A*(∫ z in Metric.ball (0:Position) 1,coulombKernel z^2)) c r := by
  let I := ∫ z in Metric.ball (0:Position) 1,coulombKernel z^2
  have hI : 0≤I := integral_nonneg (fun _ => sq_nonneg _)
  have H := potentialOf_lipschitz_bound (mixturePacketDensity_integrable hg hm hc hr hs ν)
    (mixturePacketDensity_nonneg ν g hc hr hs)
    (mixturePacketDensity_explicit_bound hg hgs hA hAb hc hr hs hrs ν) x y
  rw [mixturePacketDensity_mass hg hm hc hr hs ν,Real.norm_eq_abs] at H
  have hn0 : 0≤(n:ℝ) := Nat.cast_nonneg n
  calc
    _≤((n:ℝ)*((c*r*r^packetExponent)^(-3:ℤ)*A)*I+(n:ℝ))*‖x-y‖ := H
    _≤((n:ℝ)*((c*r*r^packetExponent)^(-3:ℤ)*A)*I+(n:ℝ))*r^3 := by gcongr
    _=(n:ℝ)*((c*r*r^packetExponent)^(-3:ℤ)*(A*I)+1)*r^3 := by ring
    _≤(3*Z)*((c*r*r^packetExponent)^(-3:ℤ)*(A*I)+1)*r^3 := by gcongr
    _=(Z/r)*initialPacketModulus (A*I) c r := by
      have He := initial_width_modulus_identity hc hr
      apply (mul_right_cancel₀ hr.ne')
      dsimp only [initialPacketModulus]
      calc
        _=3*Z*((A*I)*((c*r*r^packetExponent)^(-3:ℤ)*r^4)+r^4) := by ring
        _=3*Z*((A*I)*((c^3)⁻¹*r^(1-3*packetExponent))+r^4) := by rw [He]
        _=_ := by field_simp
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_InitialMesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology Classical
noncomputable section
namespace NeutralAtom

lemma exists_initial_band_mesh {r : ℝ} (hr : 0 < r) (hr1 : r≤1) :
    ∃ t : Finset Position,(∀ y∈t,r≤‖y‖ ∧ ‖y‖≤2*r) ∧
      (∀ y : Position,r≤‖y‖ → ‖y‖≤2*r → ∃ z∈t,‖y-z‖ ≤ r^3) ∧
      (t.card:ℝ)≤343/r^6 := by
  let S := {y : Position | r≤‖y‖ ∧ ‖y‖≤2*r}
  obtain ⟨t,ht,hcover,hcard⟩ := exists_quantitative_mesh S (R:=2*r) (ε:=r^3)
    (by positivity) (by positivity) (fun _ h => h.2)
  refine ⟨t,fun y hy => ht hy,fun y hy0 hy1 => hcover y ⟨hy0,hy1⟩,?_⟩
  have hroot : 2*r+r^3/3≤7*r/3 := by
    have H := mul_le_mul_of_nonneg_left (pow_le_one₀ hr.le hr1 (n:=2)) hr.le
    nlinarith only [H]
  have Hpow := pow_le_pow_left₀ (by positivity : 0≤2*r+r^3/3) hroot 3
  have H := hcard.trans Hpow
  apply (le_div_iff₀ (pow_pos hr 6)).mpr
  have H' : (t.card:ℝ)*r^9≤343*r^3 := by nlinarith only [H]
  have HH : ((t.card:ℝ)*r^6)*r^3≤343*r^3 := by nlinarith only [H']
  exact (mul_le_mul_iff_left₀ (pow_pos hr 3)).mp HH

theorem initial_posterior_mesh_event {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B] {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (raw : Ω → Configuration n)
    {obs : Ω → B} (_ : Measurable obs)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g) (hm : (∫ x,g x^2)=1)
    {A c r s Z T : ℝ} (hA : 0≤A) (hAb : ∀ x,g x^2≤A)
    (hc : 0 < c) (hr : 0 < r) (hr1 : r≤1) (hs : 0 < s) (hrs : r ≤ s)
    (hZ : 0≤Z) (hn : (n:ℝ)≤3*Z)
    (hpoint : ∀ y : Position,P.real {a | T≤potentialOf
      (conditionalPacketDensity P raw obs g c r s (obs a)) y} ≤ r^42) :
    ∃ G : Set B,MeasurableSet G ∧ P.real (obs ⁻¹' Gᶜ)≤343*r^36 ∧
      ∀ a∈G,∀ y : Position,r≤‖y‖ → ‖y‖≤2*r →
        potentialOf (conditionalPacketDensity P raw obs g c r s a) y≤T+
          (Z/r)*initialPacketModulus (A*(∫ z in Metric.ball (0:Position) 1,coulombKernel z^2)) c r := by
  obtain ⟨t,ht,hcover,hcard⟩ := exists_initial_band_mesh hr hr1
  let V : B → Position → ℝ := fun a => potentialOf (conditionalPacketDensity P raw obs g c r s a)
  let Bbad : Position → Set B := fun y => {a | T≤V a y}
  let E : Set B := ⋃ y∈t,Bbad y
  have hbad (y : Position) : MeasurableSet (Bbad y) := measurableSet_le measurable_const
    (measurable_conditionalPacketPotential_data P raw obs hg hgs hm hc hr hs y)
  have hE : MeasurableSet E := t.measurableSet_biUnion (fun y _ => hbad y)
  refine ⟨Eᶜ,hE.compl,?_,?_⟩
  · rw [compl_compl]
    have hpre : obs ⁻¹' E=⋃ y∈t,obs ⁻¹' Bbad y := by simp only [E,preimage_iUnion]
    rw [hpre]
    calc
      _≤∑ y∈t,P.real (obs ⁻¹' Bbad y) := measureReal_biUnion_finset_le _ _
      _≤∑ _y∈t,r^42 := Finset.sum_le_sum (fun y _ => hpoint y)
      _=(t.card:ℝ)*r^42 := by simp
      _≤(343/r^6)*r^42 := mul_le_mul_of_nonneg_right hcard (by positivity)
      _=343*r^36 := by field_simp
  · intro a ha y hy0 hy1
    obtain ⟨z,hz,hzy⟩ := hcover y hy0 hy1
    have hz' : V a z<T := by
      have Hz : a∉Bbad z := fun H => ha (Set.mem_iUnion.mpr ⟨z,Set.mem_iUnion.mpr ⟨hz,H⟩⟩)
      exact lt_of_not_ge Hz
    have HL := initial_potential_mesh_modulus hg hgs hm hA hAb hc hr hs hrs hZ hn
      (ProbabilityTheory.condDistrib raw obs P a) hzy
    change potentialOf (conditionalPacketDensity P raw obs g c r s a) y≤_
    have HH := le_abs_self (V a y-V a z)
    change |V a y-V a z|≤_ at HL
    linarith only [HL,HH,hz']
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology Classical
noncomputable section
namespace NeutralAtom

lemma retainedInverseOffset_seventh_tendsto (D : ℝ) :
    Tendsto (fun r => retainedInverseOffset D r*r^7) (𝓝[>] 0) (𝓝 0) := by
  have H := (retainedInverseOffset_scaled_tendsto D).mul
    (tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<1/50))
  simp only [mul_zero] at H
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr' : 0 < r := hr
  rw [mul_assoc,←Real.rpow_add hr']
  norm_num [Real.rpow_natCast]

lemma initialAtomicRadius_pos {ε Z : ℝ} (hε : 0<ε) (hZ : 0<Z) :
    0 < initialAtomicRadius ε Z := mul_pos hε (Real.rpow_pos_of_pos hZ _)

lemma initialAtomicRadius_tendsto {ε : ℝ} (hε : 0<ε) :
    Tendsto (initialAtomicRadius ε) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · change Tendsto (fun Z : ℝ => ε*Z^(-(1/3:ℝ))) atTop (𝓝 0)
    simpa only [mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/3)).const_mul ε
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with Z hZ
    exact initialAtomicRadius_pos hε hZ

lemma initialAtomicRadius_seventh {ε Z : ℝ} (hZ : 0<Z) :
    Z^(7/3:ℝ)*(initialAtomicRadius ε Z)^7=ε^7 := by
  rw [initialAtomicRadius,mul_pow,←Real.rpow_mul_natCast hZ.le]
  calc
    _=ε^7*(Z^(7/3:ℝ)*Z^((-(1/3:ℝ))*7)) := by ring_nf
    _=ε^7 := by rw [←Real.rpow_add hZ]; norm_num

lemma initialAtomicRadius_offset_eventually (D : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ Z : ℝ in atTop,
      retainedInverseOffset D (initialAtomicRadius ε Z)≤Z^(7/3:ℝ) := by
  have H := (retainedInverseOffset_seventh_tendsto D).comp (initialAtomicRadius_tendsto hε)
  have he := H.eventually (gt_mem_nhds (pow_pos hε 7))
  filter_upwards [he,eventually_gt_atTop (0:ℝ)] with Z hz hZ
  apply (mul_le_mul_iff_left₀ (pow_pos (initialAtomicRadius_pos hε hZ) 7)).mp
  rw [initialAtomicRadius_seventh hZ]
  exact hz.le

end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology Classical SchwartzMap
noncomputable section
namespace NeutralAtom

lemma initialAtomicRadius_potential_scale {ε Z : ℝ} (hZ : 0<Z) :
    Z^(4/3:ℝ)*initialAtomicRadius ε Z=ε*Z := by
  unfold initialAtomicRadius
  calc
    _=ε*(Z^(4/3:ℝ)*Z^(-(1/3:ℝ))) := by ring
    _=ε*Z := by rw [←Real.rpow_add hZ]; norm_num

theorem physical_initial_event_oai : ∃ εmax : ℝ,0<εmax ∧
    ∀ {ε : ℝ},0<ε → ε≤εmax →
    ∀ (D : ℝ) (g₀ : 𝓢(Position,ℝ)),(∫ w,g₀ w^2)=1 →
    (∀ w,g₀ w=g₀ (EuclideanSpace.single 0 ‖w‖)) → (∀ w,1<‖w‖ → g₀ w=0) →
    ∀ {c s : ℝ},0 < c → 0 < s → c*(1+packetExponent)*s^packetExponent≤1/2 →
    ∃ Zmin : ℕ,∀ (Z : ℕ),Zmin≤Z → ∀ (hZ : 1≤Z) {N J : ℕ}
      {ψ : Wavefunction (N+1)} {g : Gradient (N+1)},
    ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
    (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)),FormDomain χ h → normSquared χ=1 →
      energy Z ψ g≤energy Z χ h) →
    ∀ {E : ℝ},(E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g≤E+D → (N+1:ℝ)≤3*(Z:ℝ) →
    letI := rawLaw_isProbability hd.2.2.1 hn
    let P := observationLaw J (rawLaw ψ)
    let r₀ := initialAtomicRadius ε Z
    let r := fun k : Fin J => r₀*2^k.val
    ∃ G : Set (Fin J → UnorderedArray (N+1)),MeasurableSet G ∧
      P.real (tailObservation r 0 ⁻¹' Gᶜ)≤343*r₀^35 ∧
      ∀ a∈G,∀ y : Position,r₀≤‖y‖ → ‖y‖≤2*r₀ →
        potentialOf (conditionalPacketDensity P Prod.fst (tailObservation r 0) g₀ c r₀ s a) y≤
          (1/10:ℝ)*(Z:ℝ)/r₀ := by
  obtain ⟨C,hC,HC⟩ := physical_initial_potential_point
  refine ⟨1/(20*C),by positivity,?_⟩
  intro ε hε hεmax D g₀ hm hrad hg c s hc hs hq
  have hgs : HasCompactSupport (g₀ : Position → ℝ) := HasCompactSupport.intro
    (isCompact_closedBall (0:Position) 1) (fun z hz => hg z
      (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz))
  obtain ⟨A,hA,hAb⟩ := compact_packet_function_bound g₀.continuous hgs
  let I := ∫ z in Metric.ball (0:Position) 1,coulombKernel z^2
  have ht := initialAtomicRadius_tendsto hε
  have hmod := (initialPacketModulus_tendsto (A*I) c).comp ht
  have hsmall : ∀ᶠ Z : ℝ in atTop,0<Z ∧ initialAtomicRadius ε Z≤1 ∧
      initialAtomicRadius ε Z ≤ s ∧
      retainedInverseOffset D (initialAtomicRadius ε Z)≤Z^(7/3:ℝ) ∧
      initialPacketModulus (A*I) c (initialAtomicRadius ε Z)≤1/20 := by
    filter_upwards [eventually_gt_atTop (0:ℝ),
      (ht.mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
      (ht.mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds hs),
      initialAtomicRadius_offset_eventually D hε,
      hmod.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/20))] with Z hZ h1 hS hδ hM
    exact ⟨hZ,h1.le,hS.le,hδ,hM.le⟩
  obtain ⟨Zmin,hZmin⟩ := eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually hsmall)
  refine ⟨Zmin,?_⟩
  intro Z hZm hZ N J ψ g hd hn hmin E hE hbase hnum
  have := rawLaw_isProbability hd.2.2.1 hn
  dsimp only
  obtain ⟨hZr,hr1,hrs,hδ,hM⟩ := hZmin Z hZm
  have hr := initialAtomicRadius_pos hε hZr
  let P := observationLaw J (rawLaw ψ)
  let r₀ := initialAtomicRadius ε Z
  let r := fun k : Fin J => r₀*2^k.val
  have HA : ∀ x,(g₀ x)^2≤A := hAb
  obtain ⟨G,hG,hp,HG⟩ := initial_posterior_mesh_event P Prod.fst (measurable_tailObservation r 0)
    g₀.continuous hgs hm hA HA hc hr hr1 hs hrs hZr.le (by exact_mod_cast hnum)
    (HC Z hZ hd hn hmin hE hbase hnum g₀ hm hrad hg hc hr hs hq hδ)
  refine ⟨G,hG,?_,?_⟩
  · exact hp.trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr.le hr1 (by decide : 35≤36)) (by norm_num))
  · intro a ha y hy0 hy1
    have H := HG a ha y hy0 hy1
    have hCe : C*ε≤1/20 := by
      have hh := (le_div_iff₀ (by positivity : 0<20*C)).mp hεmax
      nlinarith only [hh]
    have hscale : C*(Z:ℝ)^(4/3:ℝ)=(Z:ℝ)/r₀*(C*ε) := by
      apply (mul_right_cancel₀ hr.ne')
      rw [mul_assoc,initialAtomicRadius_potential_scale hZr]
      dsimp only [r₀]
      field_simp
    change potentialOf (conditionalPacketDensity P Prod.fst (tailObservation r 0) g₀ c r₀ s a) y≤_
    rw [hscale] at H
    have HM := mul_le_mul_of_nonneg_left (add_le_add hCe hM) (div_nonneg hZr.le hr.le)
    dsimp only [I] at HM
    calc
      _≤(Z:ℝ)/r₀*(C*ε+initialPacketModulus (A*I) c r₀) := by linarith only [H]
      _≤(Z:ℝ)/r₀*(1/20+1/20) := HM
      _=(1/10:ℝ)*(Z:ℝ)/r₀ := by ring
end NeutralAtom
end

end

end OAI
end

theorem solution : type_of% @OAI.NeutralAtom.physical_initial_event_oai := @OAI.NeutralAtom.physical_initial_event_oai
