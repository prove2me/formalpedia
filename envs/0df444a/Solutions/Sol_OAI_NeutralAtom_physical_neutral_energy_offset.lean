-- Prove2me | solution 1 for OAI.NeutralAtom.physical_neutral_energy_offset
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:33:03.335917+00:00
-- url     : https://prove2.me/submissions/f9565069-df7f-46f8-bddc-3ea6a280c92e

import Mathlib
import Definitions.Def_CoulombRadii
import Definitions.Def_OAIQ062C008
import Theorems.Thm_OAI_Coulomb_atom_global_sector_minimum
import Theorems.Thm_OAI_Coulomb_atomic_predecessor_from_physical_mean
import Theorems.Thm_OAI_NeutralAtom_physical_initial_event
import Theorems.Thm_OAI_NeutralAtom_physical_propagation_good_events

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_AtomicStability
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical BigOperators
noncomputable section
namespace Coulomb

lemma atomicAttractionExcess_insert {ι : Type*} [DecidableEq ι]
    (Z : ℕ) (X : ι → Space) (s : Finset ι) (a : ι) (ha : a ∉ s) :
    atomicAttractionExcess Z X (insert a s) = atomicAttractionExcess Z X s +
      (Z:ℝ)*coulombKernel (X a) - ∑ j ∈ s, coulombKernel (X a-X j) := by
  simp only [atomicAttractionExcess, Finset.sum_insert ha, sub_self, coulombKernel, norm_zero,
    inv_zero, zero_add]
  have hsym : ∀ i, ‖X i-X a‖⁻¹ = ‖X a-X i‖⁻¹ := fun i => by rw [norm_sub_rev]
  simp_rw [hsym]
  rw [Finset.sum_add_distrib]
  ring

lemma twice_pair_kernel_ge_outer {x y : Space} (hxy : x ≠ y) (hr : ‖y‖ ≤ ‖x‖) :
    coulombKernel x ≤ 2*coulombKernel (x-y) := by
  by_cases hx : x = 0
  · subst x
    simp only [coulombKernel, norm_zero, inv_zero]
    positivity
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hxypos : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hdist : ‖x-y‖ ≤ 2*‖x‖ := (norm_sub_le x y).trans (by linarith)
  have h : 1 / ‖x‖ ≤ 2 / ‖x-y‖ :=
    (div_le_div_iff₀ hxpos hxypos).mpr (by simpa using hdist)
  simpa only [coulombKernel, one_div, div_eq_mul_inv, one_mul] using h

lemma atomicAttractionExcess_le {ι : Type*} [DecidableEq ι]
    (Z : ℕ) (X : ι → Space) (hX : Function.Injective X)
    (A : ℝ) (hA : 0 ≤ A) (s : Finset ι)
    (hc : ∀ i ∈ s, coulombKernel (X i) ≤ A) :
    atomicAttractionExcess Z X s ≤ (Z:ℝ)*(2*Z)*A := by
  induction s using Finset.strongInductionOn with
  | _ s IH =>
    by_cases hs : s.card ≤ 2*Z
    · have hp : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, coulombKernel (X i-X j) :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => coulombKernel_nonneg _
      have hsum : ∑ i ∈ s, coulombKernel (X i) ≤ (s.card:ℝ)*A := by
        simpa using Finset.sum_le_sum hc
      have hcard : (s.card:ℝ) ≤ 2*(Z:ℝ) := by exact_mod_cast hs
      unfold atomicAttractionExcess
      nlinarith [mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg Z),
        mul_le_mul_of_nonneg_right hcard hA]
    · have hne : s.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨a, ha, hmax⟩ := s.exists_max_image (fun i => ‖X i‖) hne
      have hsmall : s.erase a ⊂ s := Finset.erase_ssubset ha
      have hi := IH (s.erase a) hsmall (fun i hi => hc i (Finset.mem_of_mem_erase hi))
      have hrep : (Z:ℝ)*coulombKernel (X a) ≤ ∑ j ∈ s.erase a, coulombKernel (X a-X j) := by
        have hsum : (s.erase a).card*coulombKernel (X a) ≤
            2*(∑ j ∈ s.erase a, coulombKernel (X a-X j)) := by
          calc
            _ = ∑ _j ∈ s.erase a, coulombKernel (X a) := by simp
            _ ≤ ∑ j ∈ s.erase a, 2*coulombKernel (X a-X j) := by
              apply Finset.sum_le_sum
              intro j hj
              exact twice_pair_kernel_ge_outer (fun h =>
                (Finset.ne_of_mem_erase hj) (hX h).symm) (hmax j (Finset.mem_of_mem_erase hj))
            _ = _ := by rw [Finset.mul_sum]
        have hcard : 2*(Z:ℝ) ≤ ((s.erase a).card : ℝ) := by
          have he := Finset.card_erase_of_mem ha
          exact_mod_cast (show 2*Z ≤ (s.erase a).card by omega)
        have hp := mul_le_mul_of_nonneg_right hcard (coulombKernel_nonneg (X a))
        linarith
      rw [← Finset.insert_erase ha, atomicAttractionExcess_insert Z X (s.erase a) a
        (Finset.notMem_erase a s)]
      linarith

lemma atomicAttractionExcess_quadratic_le {n : ℕ} (Z : ℕ)
    (X : Fin n → Space) (hX : Function.Injective X) :
    atomicAttractionExcess Z X Finset.univ ≤
      (1/8:ℝ)*(∑ i, (coulombKernel (X i))^2) + 8*(Z:ℝ)^4 := by
  let H : ℝ := ∑ i, (coulombKernel (X i))^2
  have hH : 0 ≤ H := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hc (i : Fin n) (_hi : i ∈ Finset.univ) : coulombKernel (X i) ≤ Real.sqrt H :=
    Real.le_sqrt_of_sq_le (show (coulombKernel (X i))^2 ≤ H from
      Finset.single_le_sum (fun j _ => sq_nonneg (coulombKernel (X j))) (Finset.mem_univ i))
  have h := atomicAttractionExcess_le Z X hX (Real.sqrt H) (Real.sqrt_nonneg _) Finset.univ hc
  have hsq := Real.sq_sqrt hH
  change atomicAttractionExcess Z X Finset.univ ≤ (1/8:ℝ)*H + 8*(Z:ℝ)^4
  nlinarith [sq_nonneg (Real.sqrt H-8*(Z:ℝ)^2)]

lemma atom_potential_excess {n : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) (x : Configuration n) :
    nuclearPotential (atom Z hZ) x-pairPotential x =
      atomicAttractionExcess Z (position x) Finset.univ := by
  have hn : nuclearPotential (atom Z hZ) x = (Z:ℝ)*∑ i, coulombKernel (position x i) := by
    simp [nuclearPotential, attraction, atom, Finset.mul_sum]
  rw [hn, atomicAttractionExcess, ← twice_pairPotential x]
  ring

lemma H1Vector.nuclear_square_integrable_bound {n : ℕ} (ψ : H1Vector n)
    (s : Spins n) (i : Fin n) (R : Space) :
    Integrable (fun x => (coulombKernel (position x i-R))^2*‖ψ.value s x‖^2) ∧
    (∫ x, (coulombKernel (position x i-R))^2*‖ψ.value s x‖^2) ≤
      4*∑ b : Fin 3, ∫ x, ‖ψ.gradient s (i,b) x‖^2 := by
  have he (x : Configuration n) : (blockRadiusSq i (nuclearHardyCoordinates i R) x)⁻¹ =
      (coulombKernel (position x i-R))^2 := by
    rw [← hardyCoulomb_sq, hardyCoulomb_nuclear]
  simpa only [he] using ψ.hardy s i (nuclearHardyCoordinates i R)

theorem atom_form_uniform_lower {n : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) (ψ : H1Vector n) :
    -(8*(Z:ℝ)^4)*mass ψ ≤ form (atom Z hZ) ψ := by
  have hb (s : Spins n) :
      (∫ x, nuclearPotential (atom Z hZ) x*‖ψ.value s x‖^2) -
      (∫ x, pairPotential x*‖ψ.value s x‖^2) ≤
      (1/2:ℝ)*(∑ i : Fin n, ∑ b : Fin 3, ∫ x, ‖ψ.gradient s (i,b) x‖^2) +
        8*(Z:ℝ)^4*(∫ x, ‖ψ.value s x‖^2) := by
    have hi (i : Fin n) := ψ.nuclear_square_integrable_bound s i 0
    simp only [sub_zero] at hi
    have hI : Integrable (fun x => (∑ i, (coulombKernel (position x i))^2)*‖ψ.value s x‖^2) := by
      simp_rw [Finset.sum_mul]
      exact integrable_finsetSum _ fun i _ => (hi i).1
    have hL : Integrable (fun x => ‖ψ.value s x‖^2) := (ψ.value_L2 s).norm.integrable_sq
    have hB := (hI.const_mul (1/8:ℝ)).add (hL.const_mul (8*(Z:ℝ)^4))
    have hN := ψ.nuclear_integrable (atom Z hZ) s
    have hP := ψ.pair_integrable s
    change Integrable (fun x => nuclearPotential (atom Z hZ) x*‖ψ.value s x‖^2) at hN
    change Integrable (fun x => pairPotential x*‖ψ.value s x‖^2) at hP
    have he : ∀ᵐ x : Configuration n,
        nuclearPotential (atom Z hZ) x*‖ψ.value s x‖^2-pairPotential x*‖ψ.value s x‖^2 ≤
          (1/8:ℝ)*((∑ i, (coulombKernel (position x i))^2)*‖ψ.value s x‖^2) +
          8*(Z:ℝ)^4*‖ψ.value s x‖^2 := by
      filter_upwards [ae_position_injective n] with x hx
      have h := mul_le_mul_of_nonneg_right (atomicAttractionExcess_quadratic_le Z (position x) hx)
        (sq_nonneg ‖ψ.value s x‖)
      rw [← atom_potential_excess Z hZ x] at h
      nlinarith
    have hh := integral_mono_ae (hN.sub hP) hB he
    simp only [Pi.sub_apply, Pi.add_apply] at hh
    rw [integral_sub hN hP, integral_add (hI.const_mul _) (hL.const_mul _),
      integral_const_mul, integral_const_mul] at hh
    have hH : (∫ x, (∑ i, (coulombKernel (position x i))^2)*‖ψ.value s x‖^2) ≤
        4*(∑ i : Fin n, ∑ b : Fin 3, ∫ x, ‖ψ.gradient s (i,b) x‖^2) := by
      simp_rw [Finset.sum_mul]
      rw [integral_finsetSum _ (fun i _ => (hi i).1), Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => (hi i).2
    linarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun s _ => hb s)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have hk : (1/2:ℝ)*(∑ s : Spins n, ∑ i : Fin n, ∑ b : Fin 3,
      ∫ x, ‖ψ.gradient s (i,b) x‖^2) = kinetic ψ := by
    simp [kinetic, Fintype.sum_prod_type]
  rw [hk] at hs
  change nuclearEnergy (atom Z hZ) ψ - pairEnergy ψ ≤ kinetic ψ + 8*(Z:ℝ)^4*mass ψ at hs
  unfold form
  linarith

lemma atom_unrestricted_bottom_lower (Z : ℕ) (hZ : 1 ≤ Z) :
    (-(8*(Z:ℝ)^4) : EReal) ≤ unrestrictedFormBottom (atom Z hZ) := by
  apply le_iInf
  intro n
  apply le_sInf
  rintro e ⟨ψ, _ha, hm, rfl⟩
  have h := atom_form_uniform_lower Z hZ ψ
  rw [hm, mul_one] at h
  exact EReal.coe_le_coe h

lemma atom_unrestricted_bottom_ne_bot (Z : ℕ) (hZ : 1 ≤ Z) :
    unrestrictedFormBottom (atom Z hZ) ≠ ⊥ := by
  intro he
  have h := atom_unrestricted_bottom_lower Z hZ
  rw [he] at h
  exact EReal.coe_ne_bot _ (le_bot_iff.mp h)

lemma atom_unrestricted_bottom_real {n : ℕ} (Z : ℕ) (hZ : 1 ≤ Z)
    (ψ : H1Vector n) (ha : Antisymmetric ψ) (hm : mass ψ = 1) :
    ((unrestrictedFormBottom (atom Z hZ)).toReal : EReal) = unrestrictedFormBottom (atom Z hZ) := by
  apply EReal.coe_toReal
  · intro he
    have h := unrestrictedFormBottom_le_trial (atom Z hZ) ψ ha hm
    rw [he] at h
    exact EReal.coe_ne_top _ (top_le_iff.mp h)
  · exact atom_unrestricted_bottom_ne_bot Z hZ
end Coulomb
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

theorem translated_kernel_indicator_eq (x : Position) (r : ℝ) :
    (Metric.ball x r).indicator (fun y => coulombKernel (x-y)) =
      (fun y => (Metric.ball (0 : Position) r).indicator coulombKernel (x-y)) := by
  ext y
  have hh : x-y ∈ Metric.ball (0 : Position) r ↔ y ∈ Metric.ball x r := by
    simp only [Metric.mem_ball, dist_eq_norm, sub_zero, norm_sub_rev]
  by_cases hy : y ∈ Metric.ball x r <;> simp [hh, hy]

theorem translated_kernel_indicator_integrable (x : Position) (r : ℝ) :
    Integrable ((Metric.ball x r).indicator (fun y => coulombKernel (x-y))) := by
  rw [translated_kernel_indicator_eq]
  exact (integrable_comp_sub_left
    ((Metric.ball (0 : Position) r).indicator coulombKernel) x).mpr
      ((coulombKernel_integrableOn_ball r).integrable_indicator measurableSet_ball)

theorem translated_kernel_indicator_integral (x : Position) (r : ℝ) :
    (∫ y, (Metric.ball x r).indicator (fun y => coulombKernel (x-y)) y) =
      kernelBallMass r := by
  rw [translated_kernel_indicator_eq, integral_sub_left_eq_self,
    integral_indicator measurableSet_ball]
  rfl

theorem kernelBallMass_nonneg (r : ℝ) : 0 ≤ kernelBallMass r :=
  integral_nonneg (fun _ => coulombKernel_nonneg _)

theorem potential_integrable_and_bound {ρ : Position → ℝ} {x : Position} {r A : ℝ}
    (hρ : Integrable ρ) (hpos : ∀ y, 0 ≤ ρ y) (hr : 0 < r)
    (hloc : ∀ y ∈ Metric.ball x r, ρ y ≤ A) :
    Integrable (fun y => coulombKernel (x-y)*ρ y) ∧
      potentialOf ρ x ≤ A*kernelBallMass r+r⁻¹*(∫ y, ρ y) := by
  let b : Position → ℝ := fun y =>
    A*((Metric.ball x r).indicator (fun y => coulombKernel (x-y))) y+r⁻¹*ρ y
  have hb : Integrable b :=
    ((translated_kernel_indicator_integrable x r).const_mul A).add (hρ.const_mul r⁻¹)
  have hdom : ∀ y, coulombKernel (x-y)*ρ y ≤ b y := by
    intro y
    by_cases hy : y ∈ Metric.ball x r
    · simp only [b, Set.indicator_of_mem hy]
      exact (mul_le_mul_of_nonneg_left (hloc y hy) (coulombKernel_nonneg _)).trans
        (by nlinarith [mul_nonneg (inv_nonneg.mpr hr.le) (hpos y)])
    · simp only [b, Set.indicator_of_notMem hy, mul_zero, zero_add]
      have hd : r ≤ ‖x-y‖ := by
        simpa only [Metric.mem_ball, not_lt, dist_eq_norm, norm_sub_rev] using hy
      exact mul_le_mul_of_nonneg_right (inv_anti₀ hr hd) (hpos y)
  have hprod : AEStronglyMeasurable (fun y => coulombKernel (x-y)*ρ y) volume :=
    ((measurable_coulombKernel.comp (measurable_const.sub measurable_id)).aestronglyMeasurable).mul
      hρ.aestronglyMeasurable
  have hi : Integrable (fun y => coulombKernel (x-y)*ρ y) := hb.mono' hprod
    (Filter.Eventually.of_forall (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (coulombKernel_nonneg _) (hpos y))]
      exact hdom y))
  refine ⟨hi, (integral_mono hi hb hdom).trans_eq ?_⟩
  dsimp [b]
  rw [integral_add ((translated_kernel_indicator_integrable x r).const_mul A) (hρ.const_mul r⁻¹),
    integral_const_mul, integral_const_mul, translated_kernel_indicator_integral]

theorem potentialOf_nonneg {ρ : Position → ℝ} (hρ : ∀ y, 0 ≤ ρ y) (x : Position) :
    0 ≤ potentialOf ρ x := integral_nonneg (fun y => mul_nonneg (coulombKernel_nonneg _) (hρ y))

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

theorem exceptional_event_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {Y : Ω → ℝ}
    (hY : MemLp Y 2 μ) (hY0 : 0 ≤ᵐ[μ] Y)
    {S : Set Ω} (hS : MeasurableSet S) :
    (∫ z in S, Y z ∂μ) ≤
      Real.sqrt (∫ z, Y z ^ 2 ∂μ) * Real.sqrt (μ.real S) := by
  let χ : Ω → ℝ := S.indicator (fun _ => 1)
  have hχ0 : 0 ≤ᵐ[μ] χ := Filter.Eventually.of_forall fun z => by
    by_cases hz : z ∈ S <;> simp [χ, hz]
  have hχ : MemLp χ (ENNReal.ofReal 2) μ := by
    simpa [χ] using (memLp_const (1 : ℝ) (p := 2) (μ := μ)).indicator hS
  have hY' : MemLp Y (ENNReal.ofReal 2) μ := by simpa using hY
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    hY0 hχ0 hY' hχ
  have heq : (fun z => Y z * χ z) = S.indicator Y := by
    funext z
    by_cases hz : z ∈ S <;> simp [χ, hz]
  have hχsq : (fun z => χ z ^ (2 : ℝ)) = χ := by
    funext z
    by_cases hz : z ∈ S <;> simp [χ, hz]
  rw [heq, integral_indicator hS, hχsq] at h
  simpa only [χ, Real.rpow_two, integral_indicator hS, setIntegral_const,
    smul_eq_mul, mul_one, ← Real.sqrt_eq_rpow] using h

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

theorem packetKernel_support (g : Position → ℝ)
    (hg : ∀ x, 1 < ‖x‖ → g x = 0) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (z y : Position)
    (hK : packetKernel g c₁ r₀ s z y ≠ 0) :
    ‖y-z‖ ≤ packetWidth c₁ r₀ s z := by
  have ht := packetWidth_pos hc hr hs z
  by_contra! hlt
  have harg : 1 < ‖(packetWidth c₁ r₀ s z)⁻¹ • (y-z)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    have : 1 < ‖y-z‖ / packetWidth c₁ r₀ s z := (lt_div_iff₀ ht).mpr (by simpa using hlt)
    simpa only [one_mul, div_eq_mul_inv, mul_comm] using this
  exact hK (by simp [packetKernel, hg _ harg])

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

theorem packetKernel_relative_support (g : Position → ℝ)
    (hg : ∀ x, 1 < ‖x‖ → g x = 0) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (z y : Position)
    (hz : r₀ ≤ ‖z‖) (hK : packetKernel g c₁ r₀ s z y ≠ 0) :
    (1-c₁*s^packetExponent)*‖z‖ ≤ ‖y‖ ∧
      ‖y‖ ≤ (1+c₁*s^packetExponent)*‖z‖ := by
  have hd := (packetKernel_support g hg hc hr hs z y hK).trans
    (packetWidth_le c₁ r₀ s hc.le hr hs z)
  rw [max_eq_left hz] at hd
  have hn₁ := norm_sub_norm_le y z
  have hn₂ := norm_sub_norm_le z y
  rw [norm_sub_rev z y] at hn₂
  constructor <;> nlinarith

theorem packetMass_nonneg {n : ℕ} (g : Position → ℝ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    (S : Set Position) (x : Configuration n) : 0 ≤ packetMass g c₁ r₀ s S x := by
  exact Finset.sum_nonneg fun i _ => integral_nonneg fun y =>
    packetKernel_nonneg g hc hr hs (x i) y

theorem packetMass_le_rawCount {n : ℕ} (g : Position → ℝ)
    (hg : (∫ y, g y ^ 2) = 1) {c₁ r₀ s : ℝ} (hc : 0 < c₁)
    (hr : 0 < r₀) (hs : 0 < s) (S T : Set Position)
    (hST : ∀ z y, y ∈ S → packetKernel g c₁ r₀ s z y ≠ 0 → z ∈ T)
    (x : Configuration n) : packetMass g c₁ r₀ s S x ≤ rawCount T x := by
  classical
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : x i ∈ T
  · simp only [Set.indicator_of_mem hi]
    calc
      (∫ y in S, packetKernel g c₁ r₀ s (x i) y)
        ≤ ∫ y, packetKernel g c₁ r₀ s (x i) y :=
          setIntegral_le_integral (integrable_packetKernel g hg hc hr hs (x i))
            (Filter.Eventually.of_forall (packetKernel_nonneg g hc hr hs (x i)))
      _ = 1 := integral_packetKernel g hg hc hr hs (x i)
  · simp only [Set.indicator_of_notMem hi]
    have hz : (∫ y in S, packetKernel g c₁ r₀ s (x i) y) = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun y hy => by
        by_contra hK
        exact hi (hST (x i) y hy hK)
    exact hz.le

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

end NeutralAtom
end

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

theorem measurable_packetMass {n : ℕ} {g : Position → ℝ} (hg : Continuous g)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    (S : Set Position) : Measurable (packetMass (n := n) g c₁ r₀ s S) := by
  have hjoint := (continuous_packetKernel hg hc hr hs).stronglyMeasurable
  have hint : Measurable (fun z : Position => ∫ y in S, packetKernel g c₁ r₀ s z y) :=
    (hjoint.integral_prod_right' (ν := volume.restrict S)).measurable
  exact Finset.measurable_sum _ (fun i _ => hint.comp (measurable_pi_apply i))

theorem packetMass_le_number {n : ℕ} (g : Position → ℝ) (hg : (∫ y, g y^2) = 1)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    (S : Set Position) (x : Configuration n) : packetMass g c₁ r₀ s S x ≤ n := by
  exact (packetMass_le_rawCount g hg hc hr hs S Set.univ (by simp) x).trans
    (rawCount_le_number Set.univ x)

theorem packetMass_memLp {n : ℕ} {g : Position → ℝ} (hg : Continuous g)
    (hgnorm : (∫ y, g y^2) = 1) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (S : Set Position)
    (μ : Measure (Configuration n)) [IsFiniteMeasure μ] :
    MemLp (packetMass g c₁ r₀ s S) 2 μ := by
  apply MemLp.of_bound (measurable_packetMass hg hc hr hs S).aestronglyMeasurable (n : ℝ)
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (packetMass_nonneg g hc hr hs S x)]
    using packetMass_le_number g hgnorm hc hr hs S x

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

theorem rawPacketDensity_setIntegral {n : ℕ} (g : Position → ℝ)
    (hgnorm : (∫ y, g y^2)=1) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    (S : Set Position) (x : Configuration n) :
    (∫ y in S, rawPacketDensity g c₁ r₀ s x y) = packetMass g c₁ r₀ s S x := by
  unfold rawPacketDensity packetMass
  exact integral_finsetSum _ (fun i _ => (integrable_packetKernel g hgnorm hc hr hs (x i)).integrableOn)

theorem rawPacketDensity_prod_restrict_integrable {n : ℕ} {g : Position → ℝ}
    (hg : Continuous g) (hgnorm : (∫ y, g y^2)=1) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    (ν : Measure (Configuration n)) [IsFiniteMeasure ν] (S : Set Position) :
    Integrable (fun xy : Configuration n × Position => rawPacketDensity g c₁ r₀ s xy.1 xy.2)
      (ν.prod (volume.restrict S)) := by
  apply (integrable_prod_iff (continuous_rawPacketDensity hg hc hr hs).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun x => (rawPacketDensity_integrable g hgnorm hc hr hs x).integrableOn)
  · have he : (fun x : Configuration n => ∫ y in S, ‖rawPacketDensity g c₁ r₀ s x y‖) =
        packetMass g c₁ r₀ s S := by
      funext x
      simp only [Real.norm_eq_abs, abs_of_nonneg (rawPacketDensity_nonneg g hc hr hs x _),
        rawPacketDensity_setIntegral g hgnorm hc hr hs]
    rw [he]
    exact (packetMass_memLp hg hgnorm hc hr hs S ν).integrable (by norm_num)

theorem mixturePacketDensity_setIntegral {n : ℕ} {g : Position → ℝ}
    (hg : Continuous g) (hgnorm : (∫ y, g y^2)=1) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    (ν : Measure (Configuration n)) [IsFiniteMeasure ν] (S : Set Position) :
    (∫ y in S, mixturePacketDensity ν g c₁ r₀ s y) =
      ∫ x, packetMass g c₁ r₀ s S x ∂ν := by
  have hi : Integrable (Function.uncurry (fun y x => rawPacketDensity g c₁ r₀ s x y))
      ((volume.restrict S).prod ν) :=
    (rawPacketDensity_prod_restrict_integrable hg hgnorm hc hr hs ν S).swap
  unfold mixturePacketDensity
  rw [integral_integral_swap hi]
  simp_rw [rawPacketDensity_setIntegral g hgnorm hc hr hs]

theorem conditionalPacketDensity_mass {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    {n : ℕ} (P : Measure Ω) [IsFiniteMeasure P]
    (raw : Ω → Configuration n) (obs : Ω → B)
    {g : Position → ℝ} (hg : Continuous g) (hgnorm : (∫ y, g y^2)=1)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (datum : B) :
    (∫ y, conditionalPacketDensity P raw obs g c₁ r₀ s datum y) = n :=
  mixturePacketDensity_mass hg hgnorm hc hr hs _

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

theorem conditionalPacketDensity_eq_condExp {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    {n : ℕ} (P : Measure Ω) [IsFiniteMeasure P]
    (ν : Measure (Configuration n)) [IsFiniteMeasure ν]
    {raw : Ω → Configuration n} {obs : Ω → B}
    (hraw : MeasurePreserving raw P ν) (hobs : Measurable obs)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (y : Position) :
    (fun sample => conditionalPacketDensity P raw obs g c₁ r₀ s (obs sample) y) =ᵐ[P]
      P[fun sample => rawPacketDensity g c₁ r₀ s (raw sample) y |
        MeasurableSpace.comap obs inferInstance] := by
  have hf : StronglyMeasurable (fun x : Configuration n => rawPacketDensity g c₁ r₀ s x y) :=
    ((continuous_rawPacketDensity hg hc hr hs).comp
      (continuous_id.prodMk (continuous_const (y := y)))).stronglyMeasurable
  exact (ProbabilityTheory.condExp_ae_eq_integral_condDistrib hobs hraw.measurable.aemeasurable hf
    (hraw.integrable_comp_of_integrable (rawPacketDensity_integrable_configuration hg hgs hc hr hs ν y))).symm

theorem conditionalPacketDensity_annulus_eq_condExp {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B]
    {n : ℕ} (P : Measure Ω) [IsFiniteMeasure P]
    (ν : Measure (Configuration n)) [IsFiniteMeasure ν]
    {raw : Ω → Configuration n} {obs : Ω → B}
    (hraw : MeasurePreserving raw P ν) (hobs : Measurable obs)
    {g : Position → ℝ} (hg : Continuous g) (hgnorm : (∫ y, g y^2)=1)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (S : Set Position) :
    (fun sample => ∫ y in S, conditionalPacketDensity P raw obs g c₁ r₀ s (obs sample) y) =ᵐ[P]
      P[fun sample => packetMass g c₁ r₀ s S (raw sample) |
        MeasurableSpace.comap obs inferInstance] := by
  have hf := (measurable_packetMass (n := n) hg hc hr hs S).stronglyMeasurable
  have hi := (packetMass_memLp hg hgnorm hc hr hs S ν).integrable (by norm_num)
  have he := ProbabilityTheory.condExp_ae_eq_integral_condDistrib hobs
    hraw.measurable.aemeasurable hf (hraw.integrable_comp_of_integrable hi)
  exact (he.trans (Filter.Eventually.of_forall (fun sample =>
    (mixturePacketDensity_setIntegral hg hgnorm hc hr hs _ S).symm))).symm

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

theorem observationLaw_rawProjection {n J : ℕ} (ν : Measure (Configuration n)) :
    MeasurePreserving Prod.fst (observationLaw J ν) ν := measurePreserving_fst

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

theorem observationSigma_le {n J : ℕ} (r : Fin J → ℝ) (j : ℕ) :
    observationSigma (n := n) r j ≤ (inferInstance : MeasurableSpace (ObservationSample n J)) :=
  measurable_iff_comap_le.mp (measurable_tailObservation r j)

theorem measurable_eraseEarlierArrays {n J : ℕ} (j : ℕ) :
    Measurable (eraseEarlierArrays (n := n) (J := J) j) := by
  apply Measurable.of_eval
  intro k
  by_cases hj : j ≤ k.val
  · simpa only [eraseEarlierArrays, ite_eq_left hj] using (measurable_pi_apply k)
  · simpa only [eraseEarlierArrays, ite_eq_right hj] using
      (measurable_const : Measurable (fun _ : Fin J → UnorderedArray n => forgetOrder (0 : Configuration n)))

theorem tailObservation_erase {n J : ℕ} (r : Fin J → ℝ) {i j : ℕ} (hij : i ≤ j) :
    tailObservation (n := n) r j = eraseEarlierArrays j ∘ tailObservation r i := by
  funext sample k
  by_cases hj : j ≤ k.val
  · simp only [tailObservation, eraseEarlierArrays, Function.comp_apply,
      ite_eq_left hj, ite_eq_left (hij.trans hj)]
  · simp only [tailObservation, eraseEarlierArrays, Function.comp_apply, ite_eq_right hj]

theorem observationSigma_antitone {n J : ℕ} (r : Fin J → ℝ) :
    Antitone (observationSigma (n := n) r) := by
  intro i j hij
  unfold observationSigma
  rw [tailObservation_erase r hij, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_iff_comap_le.mp (measurable_eraseEarlierArrays j))

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
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_RawAnnularMoment
attribute [-instance] _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace NeutralAtom
lemma raw_second_moment_asH1 {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) {S : Set Position} (hS : MeasurableSet S) :
    (∫ x,(rawCount S x)^2 ∂rawLaw ψ)=
      Coulomb.localCountSecondMoment (asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1) S := by
  rw [integral_rawLaw hd.2.2.1,rawExpectation_eq_stateWeightedIntegral hd.2.2.1
    ((measurable_rawCount hS).pow_const 2) (C:=(n:ℝ)^2) (fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (rawCount_nonneg S x) (rawCount_le_number S x) 2)]
  have H := asH1_potentialForm ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1
    (fun x => (Coulomb.localCount S x)^2)
  exact H.symm

lemma atomic_raw_annular_second_moment {α β : ℝ} (hα : 0<α) (hαβ : α<β) :
    ∃ C : ℝ,0≤C ∧ ∀ {n : ℕ} (Z : ℕ) (hZ : 1≤Z) {ψ : Wavefunction n} {g : Gradient n},
    FormDomain ψ g → normSquared ψ=1 →
    ∀ {E D : ℝ}, (E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g≤E+D → 0≤D → ∀ {r : ℝ},0 < r →
    (∫ x,(rawCount {y : Position | α*r<‖y‖ ∧ ‖y‖<β*r} x)^2 ∂rawLaw ψ)≤
      C*(Coulomb.screenMass D r)^2 := by
  obtain ⟨C,hC,HC⟩ := Coulomb.atomic_annular_second_moment hα hαβ
  refine ⟨C,hC,?_⟩
  intro n Z hZ ψ g hd hn E D hE he hD r hr
  have hS : MeasurableSet {y : Position | α*r<‖y‖ ∧ ‖y‖<β*r} :=
    (measurableSet_lt measurable_const continuous_norm.measurable).inter
      (measurableSet_lt continuous_norm.measurable measurable_const)
  rw [raw_second_moment_asH1 hd hS]
  apply HC (Coulomb.atom Z hZ) (fun _ => rfl) _ (asH1_antisymmetric hd)
    ((asH1_mass ..).trans hn) hE _ hD hr
  rwa [asH1_energy Z hZ]

lemma packet_shell_center {g : Position → ℝ} (hg : ∀ x,1<‖x‖ → g x=0)
    {c r₀ s r : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀) (hs : 0 < s) (hrr : r₀ ≤ r)
    (hq : c*s^packetExponent≤1/4) {z y : Position}
    (hy : r≤‖y‖ ∧ ‖y‖<2*r) (hK : packetKernel g c r₀ s z y≠0) :
    r/2<‖z‖ ∧ ‖z‖<4*r := by
  have hr : 0 < r := hr₀.trans_le hrr
  by_cases hz : r₀≤‖z‖
  · have H := packetKernel_relative_support g hg hc hr₀ hs z y hz hK
    have hn := norm_nonneg z
    constructor <;> nlinarith
  · have hd := (packetKernel_support g hg hc hr₀ hs z y hK).trans
      (packetWidth_le c r₀ s hc.le hr₀ hs z)
    rw [max_eq_right (le_of_not_ge hz)] at hd
    have hdiff := norm_sub_norm_le y z
    have hq' := mul_le_mul_of_nonneg_right hq hr₀.le
    constructor <;> nlinarith [norm_nonneg z]
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
namespace Coulomb
lemma atom_sectorFormBottom_antitone (Z : ℕ) (hZ : 1≤Z) :
    Antitone (sectorFormBottom (atom Z hZ)) := by
  intro a b hab
  rw [←NeutralAtom.sectorEnergy_eq_formBottom Z hZ,←NeutralAtom.sectorEnergy_eq_formBottom Z hZ]
  exact NeutralAtom.sectorEnergy_antitone Z hab

lemma atom_sectorFormBottom_real (Z : ℕ) (hZ : 1≤Z) (n : ℕ) :
    ((sectorFormBottom (atom Z hZ) n).toReal:EReal)=sectorFormBottom (atom Z hZ) n := by
  apply EReal.coe_toReal
  · intro he
    have H : sectorFormBottom (atom Z hZ) n≤0 := by
      rw [←NeutralAtom.sectorEnergy_eq_formBottom Z hZ]
      exact NeutralAtom.sectorEnergy_nonpos Z n
    rw [he] at H
    exact EReal.coe_ne_top (0:ℝ) (by simpa using top_le_iff.mp H)
  · intro he
    have H := (atom_unrestricted_bottom_lower Z hZ).trans
      (iInf_le (fun k => sectorFormBottom (atom Z hZ) k) n)
    rw [he] at H
    exact EReal.coe_ne_bot _ (le_bot_iff.mp H)

end Coulomb

end
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical

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
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_CoreMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace NeutralAtom

lemma fixedCoreMomentBound_pos (t : ℝ) : 0<fixedCoreMomentBound t := by
  unfold fixedCoreMomentBound
  have hs : 0≤∑' k : ℕ, (observedDeficitCoefficient (fun _ : Fin 1 => t/16) 0 (t/4)*
      (1+((k+1:ℕ):ℝ))^3)^2*Real.exp (-(k:ℝ)) :=
    tsum_nonneg (fun _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  positivity

end NeutralAtom
end

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

lemma measurable_conditionalPacketDensity_data {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (raw : Ω → Configuration n) (obs : Ω → B)
    {g : Position → ℝ} (hg : Continuous g) {c r₀ s : ℝ}
    (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s) (y : Position) :
    Measurable (fun datum => conditionalPacketDensity P raw obs g c r₀ s datum y) := by
  exact (((continuous_rawPacketDensity hg hc hr hs).comp
    (continuous_id.prodMk continuous_const)).stronglyMeasurable.integral_kernel
      (κ:=ProbabilityTheory.condDistrib raw obs P)).measurable

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

end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PropagationBarrierBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

lemma propagationGamma_pos {B : ℝ} (hB : 0<B) : 0<propagationGamma B := by
  unfold propagationGamma
  positivity

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PropagationConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

lemma propagation_constants_exist {B C : ℝ} (hB : 0<B) (hC : B≤C) :
    Nonempty (PropagationConstants B C) := by
  let l1 := propagationGamma B/2
  let l2 := l1/4
  have h1 : 0<l1 := by dsimp [l1]; exact div_pos (propagationGamma_pos hB) (by norm_num)
  have h2 : 0<l2 := by dsimp [l2]; positivity
  have hgap : 0<l1-l2 := by dsimp [l2]; linarith only [h1]
  let L := max 3 (C/l2)
  have hL : 2<L := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hL1 : 1≤L := by linarith only [hL]
  have hCL : C≤l2*L := by
    have H := (div_le_iff₀ h2).mp (le_max_right 3 (C/l2))
    simpa only [mul_comm] using H
  have hCL4 : C≤l2*L^4 := by
    calc
      C≤C*L^3 := le_mul_of_one_le_right (hB.le.trans hC) (one_le_pow₀ hL1)
      _≤(l2*L)*L^3 := mul_le_mul_of_nonneg_right hCL (pow_nonneg (zero_le_one.trans hL1) 3)
      _=l2*L^4 := by ring
  let e := min ((l1-l2)/16) (3*B/(16*(2*L)^4))
  have he : 0<e := lt_min (by positivity) (by positivity)
  have he1 : e≤(l1-l2)/16 := min_le_left _ _
  have he2 : e*(2*L)^4≤3*B/16 := by
    have H := min_le_right ((l1-l2)/16) (3*B/(16*(2*L)^4))
    have HD : 0<(2*L)^4 := by positivity
    exact (le_div_iff₀ HD).mp (by convert H using 1; ring)
  let ξ := min (l2/2) (min ((l1-l2)/64) (B/4))
  have hξ : 0<ξ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hξ1 : ξ≤l2/2 := min_le_left _ _
  have hξ2 : ξ≤(l1-l2)/64 := (min_le_right _ _).trans (min_le_left _ _)
  have hξ3 : ξ≤B/4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨⟨L,l1,l2,e,ξ,hL,h2,?_,?_,hCL4,he,hξ,?_,?_,?_,?_⟩⟩
  · dsimp [l2]; linarith only [h1]
  · dsimp [l1]; linarith only [propagationGamma_pos hB]
  · linarith only [hξ1,h2]
  · linarith only [hξ3,hB]
  · linarith only [hξ2,he1,hgap]
  · nlinarith only [he2]

lemma tfReaction_posFactor {v : ℝ} (hv : 0<v) :
    tfReaction v=(4*Real.pi*kTF*Real.sqrt v)*v := by
  have he : v^(3/2:ℝ)=v*Real.sqrt v := by
    rw [show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add hv,Real.rpow_one,Real.sqrt_eq_rpow]
  unfold tfReaction
  rw [max_eq_left hv.le,he]
  ring

lemma initial_constants_exist {εmax : ℝ} (hεmax : 0<εmax) :
    ∃ ε B : ℝ,0<ε ∧ ε≤εmax ∧ 0<B ∧ B≤ε^3/10 ∧
      tfReaction (2*ε^3)≤(3/40:ℝ)*ε^3 ∧
      4*Real.pi*kTF*Real.sqrt B≤19/2 := by
  have hcont : Continuous (fun ε : ℝ => 8*Real.pi*kTF*Real.sqrt (2*ε^3)) := by fun_prop
  have hcontB : Continuous (fun ε : ℝ => 4*Real.pi*kTF*Real.sqrt (ε^3/10)) := by fun_prop
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0,ε<εmax ∧
      8*Real.pi*kTF*Real.sqrt (2*ε^3)<3/40 ∧
      4*Real.pi*kTF*Real.sqrt (ε^3/10)<19/2 := by
    have ht1 : Tendsto (fun ε : ℝ => 8*Real.pi*kTF*Real.sqrt (2*ε^3)) (𝓝 0) (𝓝 0) := by
      simpa using hcont.tendsto 0
    have ht2 : Tendsto (fun ε : ℝ => 4*Real.pi*kTF*Real.sqrt (ε^3/10)) (𝓝 0) (𝓝 0) := by
      simpa using hcontB.tendsto 0
    have h1 := ht1.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<3/40))
    have h2 := ht2.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<19/2))
    exact ((gt_mem_nhds hεmax).and (h1.and h2)).filter_mono nhdsWithin_le_nhds
  have hpositive : ∀ᶠ ε : ℝ in 𝓝[>] 0,0<ε := self_mem_nhdsWithin
  obtain ⟨ε,hε,hεm,hR,hB⟩ := (hpositive.and hsmall).exists
  have hεp : 0<ε := hε
  refine ⟨ε,ε^3/10,hεp,hεm.le,by positivity,le_rfl,?_,hB.le⟩
  rw [tfReaction_posFactor (by positivity)]
  have H := mul_le_mul_of_nonneg_right hR.le (pow_nonneg hεp.le 3)
  nlinarith only [H]

lemma initial_scaled_gates {ε B Z r : ℝ} (hZ : 0<Z) (hr : 0 < r)
    (hc : Z*r^3=ε^3) (hR : tfReaction (2*ε^3)≤(3/40:ℝ)*ε^3) :
    4*(Z/(80*r^3))*r^2≤(1/20:ℝ)*Z/r ∧
    tfReaction (2*Z/r)≤6*(Z/(80*r^3)) := by
  constructor
  · apply (add_le_add_iff_left B).mp
    exact le_of_eq (by field_simp; ring)
  · have he : 2*Z/r=(2*ε^3)/r^4 := by rw [←hc]; field_simp
    rw [he,tfReaction_div_fourth _ hr]
    calc
      _≤((3/40:ℝ)*ε^3)/r^6 := div_le_div_of_nonneg_right hR (pow_pos hr 6).le
      _=6*(Z/(80*r^3)) := by rw [←hc]; field_simp; ring
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PropagationAverage
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
noncomputable section
namespace NeutralAtom
section Average
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem continuous_average_of_ball_bounds {f : Ω → Position → ℝ}
    (hf : ∀ o, Continuous (f o)) (hm : Measurable (Function.uncurry f))
    (hb : ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R → |f o x| ≤ C) :
    Continuous (fun x => ∫ o, f o x ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨C,hC⟩ := hb (‖x₀‖+1)
  apply continuousAt_of_dominated
    (Eventually.of_forall (fun x => (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable))
    (bound := fun _ => C) ?_ (integrable_const C)
    (Eventually.of_forall (fun o => (hf o).continuousAt))
  filter_upwards [Metric.ball_mem_nhds x₀ (by norm_num : (0:ℝ)<1)] with x hx
  filter_upwards [] with o
  have hdist : ‖x-x₀‖<1 := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
  have hn : ‖x‖≤‖x₀‖+1 := by
    have h := norm_add_le (x-x₀) x₀
    rw [sub_add_cancel] at h
    linarith
  change ‖f o x‖ ≤ C
  simpa only [Real.norm_eq_abs] using hC o x (by simpa using hn)

end Average
end NeutralAtom

end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PropagationDatumRegularity
attribute [-instance] _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

lemma atomic_screenedField_nuclear {ρ : Position → ℝ} (hi : Integrable ρ)
    (hc : Continuous (potentialOf ρ)) (Z : ℝ) :
    WeakNuclearSubsolution (fun x => Z*coulombKernel x-potentialOf ρ x) Z univ
      (fun x => 4*Real.pi*ρ x) := by
  change WeakNuclearSubsolution (fun x => Z*coulombKernel x+(-potentialOf ρ x)) Z univ _
  apply (weakNuclearSubsolution_offset_iff hc.neg).2
  intro φ hφ hφc ht hp
  have H := potentialOf_weakLaplacian hi φ hφ hφc ht
  have H' : (∫ x,(-potentialOf ρ x)*coordinateLaplacian φ x)=
      ∫ x,(4*Real.pi*ρ x)*φ x := by
    simp only [neg_mul,integral_neg] at H ⊢
    rw [H]
    simp only [neg_neg]
  exact H'.ge

lemma conditionalPacketField_nuclear {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (raw : Ω → Configuration n) (obs : Ω → A)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g)
    (hm : (∫ z,g z^2)=1) {c r₀ s : ℝ}
    (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s) (datum : A) (Z : ℝ) :
    WeakNuclearSubsolution (fun x => Z*coulombKernel x-potentialOf
      (conditionalPacketDensity P raw obs g c r₀ s datum) x) Z univ
      (fun x => 4*Real.pi*conditionalPacketDensity P raw obs g c r₀ s datum x) :=
  atomic_screenedField_nuclear (mixturePacketDensity_integrable hg hm hc hr hs _)
    (conditionalPacketPotential_continuous P raw obs hg hgs hm hc hr hs datum) Z
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PosteriorDensityContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
lemma mixturePacketDensity_continuous {n : ℕ} (ν : Measure (Configuration n)) [IsProbabilityMeasure ν]
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g) {c r s : ℝ}
    (hc : 0 < c) (hr : 0 < r) (hs : 0 < s) : Continuous (mixturePacketDensity ν g c r s) := by
  obtain ⟨A,hA,hAb⟩ := compact_packet_function_bound hg hgs
  change Continuous (fun x => ∫ o,rawPacketDensity g c r s o x ∂ν)
  have hb : ∀ D : ℝ,∃ C : ℝ,∀ (o : Configuration n) x,x∈Metric.closedBall 0 D → |rawPacketDensity g c r s o x|≤C := by
    intro D
    refine ⟨n*((c*r*(min r s)^packetExponent)^(-3:ℤ)*A),fun o x _ => ?_⟩
    rw [abs_of_nonneg (rawPacketDensity_nonneg g hc hr hs o x)]
    exact rawPacketDensity_bound hA hAb hc hr hs o x
  have hj : Continuous (fun z : Configuration n×Position => rawPacketDensity g c r s z.1 z.2) :=
    continuous_rawPacketDensity hg hc hr hs
  have hx : ∀ o : Configuration n,Continuous (rawPacketDensity g c r s o) := by
    intro o
    exact Continuous.uncurry_left (f:=rawPacketDensity g c r s) o hj
  exact continuous_average_of_ball_bounds (μ:=ν) (f:=fun (o : Configuration n) (x : Position) => rawPacketDensity g c r s o x) hx hj.measurable hb

lemma conditionalPacketDensity_continuous {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (raw : Ω → Configuration n) (obs : Ω → A)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g) {c r s : ℝ}
    (hc : 0 < c) (hr : 0 < r) (hs : 0 < s) (a : A) :
    Continuous (conditionalPacketDensity P raw obs g c r s a) :=
  mixturePacketDensity_continuous _ hg hgs hc hr hs

lemma measurable_conditionalPacketDensity_joint {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (raw : Ω → Configuration n) (obs : Ω → A)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g) {c r s : ℝ}
    (hc : 0 < c) (hr : 0 < r) (hs : 0 < s) :
    Measurable (fun z : A×Position => conditionalPacketDensity P raw obs g c r s z.1 z.2) := by
  have H : Measurable (fun z : Position×A => conditionalPacketDensity P raw obs g c r s z.2 z.1) :=
    measurable_uncurry_of_continuous_of_measurable
      (conditionalPacketDensity_continuous P raw obs hg hgs hc hr hs)
      (measurable_conditionalPacketDensity_data P raw obs hg hc hr hs)
  exact H.comp measurable_swap
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
lemma ae_all_position_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {f g : Ω → Position → ℝ} (hf : ∀ o,Continuous (f o)) (hg : ∀ o,Continuous (g o))
    (he : ∀ x,∀ᵐ o ∂P,f o x=g o x) : ∀ᵐ o ∂P,f o=g o := by
  obtain ⟨S,hSc,hSd⟩ := TopologicalSpace.exists_countable_dense Position
  let := hSc.to_subtype
  have H : ∀ᵐ o ∂P,∀ x : S,f o x=g o x := ae_all_iff.mpr (fun x => he x)
  filter_upwards [H] with o ho
  exact Continuous.ext_on hSd (hf o) (hg o) (fun x hx => ho ⟨x,hx⟩)

theorem posteriorPacketDensity_tower {n J : ℕ} (ν : Measure (Configuration n)) [IsProbabilityMeasure ν]
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g) {c r₀ s : ℝ}
    (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s) (r : Fin J → ℝ) {i j : ℕ} (hij : i≤j) :
    let P := observationLaw J ν
    let μi := fun o => conditionalPacketDensity P Prod.fst (tailObservation r i) g c r₀ s (tailObservation r i o)
    ∀ᵐ o ∂P,posteriorAverage P (tailObservation r j) μi (tailObservation r j o)=
      conditionalPacketDensity P Prod.fst (tailObservation r j) g c r₀ s (tailObservation r j o) := by
  let P := observationLaw J ν
  let oi := tailObservation (n:=n) r i
  let oj := tailObservation (n:=n) r j
  let μi := fun o => conditionalPacketDensity P Prod.fst oi g c r₀ s (oi o)
  have hoi : Measurable oi := measurable_tailObservation r i
  have hoj : Measurable oj := measurable_tailObservation r j
  have hμ : Measurable (Function.uncurry μi) :=
    (measurable_conditionalPacketDensity_joint P Prod.fst oi hg hgs hc hr hs).comp (hoi.prodMap measurable_id)
  obtain ⟨A,hA,hAb⟩ := conditionalPacketDensity_bounded P Prod.fst oi hg hgs hc hr hs
  have hb : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |μi o x|≤C := by
    intro D
    refine ⟨A,fun o x _ => ?_⟩
    change |conditionalPacketDensity P Prod.fst oi g c r₀ s (oi o) x|≤A
    simpa only [abs_of_nonneg (conditionalPacketDensity_nonneg P Prod.fst oi g hc hr hs (oi o) x)] using hAb (oi o) x
  apply ae_all_position_eq P
    (fun o => continuous_average_of_ball_bounds
      (fun v => conditionalPacketDensity_continuous P Prod.fst oi hg hgs hc hr hs (oi v)) hμ hb)
    (fun o => conditionalPacketDensity_continuous P Prod.fst oj hg hgs hc hr hs (oj o))
  intro x
  have hi : (fun o => μi o x)=ᵐ[P]
      P[fun o => rawPacketDensity g c r₀ s o.1 x | observationSigma r i] :=
    conditionalPacketDensity_eq_condExp P ν (observationLaw_rawProjection ν) hoi hg hgs hc hr hs x
  have hj : (fun o => conditionalPacketDensity P Prod.fst oj g c r₀ s (oj o) x)=ᵐ[P]
      P[fun o => rawPacketDensity g c r₀ s o.1 x | observationSigma r j] :=
    conditionalPacketDensity_eq_condExp P ν (observationLaw_rawProjection ν) hoj hg hgs hc hr hs x
  have hix := integrable_section_of_ball_bounds (μ:=P) hμ hb x
  have ha := ProbabilityTheory.condExp_ae_eq_integral_condDistrib_id hoj hix
  exact ha.symm.trans ((condExp_congr_ae hi).trans
    ((condExp_condExp_of_le (observationSigma_antitone r hij) (observationSigma_le r i)).trans hj.symm))
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_CompactRandomField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter ProbabilityTheory
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
section Compact
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {f : Ω → Position → ℝ} {R : ℝ}

lemma compact_random_field_integrable
    (hm : Measurable (Function.uncurry f))
    (hb : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |f o x|≤C)
    (hs : ∀ᵐ o ∂P,∀ x,R≤‖x‖ → f o x=0) :
    Integrable (Function.uncurry f) (P.prod volume) := by
  obtain ⟨C,hC⟩ := hb R
  let g := (Metric.closedBall (0:Position) R).indicator (fun _ => max C 0)
  have hgm : Measurable g := measurable_const.indicator measurableSet_closedBall
  have hgi : Integrable g := (integrable_indicator_iff measurableSet_closedBall).2
    (integrableOn_const (C:=max C 0) (isCompact_closedBall (0:Position) R).measure_ne_top)
  apply (hgi.comp_snd P).mono' hm.aestronglyMeasurable
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hm.norm (hgm.comp measurable_snd))).2
  filter_upwards [hs] with o ho
  apply Eventually.of_forall
  intro x
  change ‖f o x‖≤g x
  by_cases hx : x∈Metric.closedBall (0:Position) R
  · simpa only [g,Set.indicator_of_mem hx,Real.norm_eq_abs] using (hC o x hx).trans (le_max_left C 0)
  · have hRx : R≤‖x‖ := le_of_lt (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hx)
    simp only [ho x hRx,g,Set.indicator_of_notMem hx,norm_zero,le_refl]

lemma PropagationDatum.error_product_integrable {B C r Z L : ℝ} {μ : Ω → Position → ℝ}
    (d : PropagationDatum P B C r Z L μ) :
    Integrable (Function.uncurry d.error) (P.prod volume) :=
  compact_random_field_integrable d.error_measurable d.error_bounds
    (d.invariant.mono (fun _ h => h.error_support))
end Compact

section Posterior
variable {Ω A : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace A]
variable {P : Measure Ω} [IsProbabilityMeasure P] {f : Ω → Position → ℝ} {R : ℝ}
variable (obs : Ω → A) (ho : Measurable obs)

include ho
lemma posteriorAverage_support_ae (hs : ∀ᵐ o ∂P,∀ x,R≤‖x‖ → f o x=0) :
    ∀ᵐ o ∂P,∀ x,R≤‖x‖ → posteriorAverage P obs f (obs o) x=0 := by
  filter_upwards [posterior_ae P obs ho hs] with o hoi
  intro x hx
  exact integral_eq_zero_of_ae (hoi.mono (fun v hv => hv x hx))

lemma posteriorAverage_integral (hm : Measurable (Function.uncurry f))
    (hb : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |f o x|≤C) (x : Position) :
    (∫ o,posteriorAverage P obs f (obs o) x ∂P)=∫ o,f o x ∂P := by
  have he := ProbabilityTheory.condExp_ae_eq_integral_condDistrib_id ho
    (integrable_section_of_ball_bounds (μ:=P) hm hb x)
  calc
    _ = ∫ o,P[fun v => f v x | MeasurableSpace.comap obs inferInstance] o ∂P := integral_congr_ae he.symm
    _ = _ := integral_condExp ho.comap_le

lemma posteriorAverage_total_integral (hm : Measurable (Function.uncurry f))
    (hb : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |f o x|≤C)
    (hs : ∀ᵐ o ∂P,∀ x,R≤‖x‖ → f o x=0) :
    (∫ o,(∫ x,posteriorAverage P obs f (obs o) x) ∂P)=∫ o,(∫ x,f o x) ∂P := by
  have hm' : Measurable (fun z : Ω×Position => posteriorAverage P obs f (obs z.1) z.2) :=
    (posteriorAverage_joint_measurable P obs hm).comp (ho.prodMap measurable_id)
  have hb' : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |posteriorAverage P obs f (obs o) x|≤C := by
    intro D
    obtain ⟨C,hC⟩ := posteriorAverage_uniform_bounds P obs hb D
    exact ⟨C,fun o => hC (obs o)⟩
  have hi := compact_random_field_integrable hm hb hs
  have hi' := compact_random_field_integrable hm' hb' (posteriorAverage_support_ae obs ho hs)
  rw [integral_integral_swap hi',integral_integral_swap hi]
  exact integral_congr_ae (Eventually.of_forall (fun x => posteriorAverage_integral obs ho hm hb x))
end Posterior
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_InitialDatum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
section Error
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {μ p : Ω → Position → ℝ} {bad : Ω → Prop} {r R : ℝ}

lemma shell_error_product_integrable (hm : Measurable (Function.uncurry μ))
    (hb : MeasurableSet {o | bad o})
    (hbm : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |μ o x|≤C) :
    Integrable (fun z : Ω×Position => if bad z.1 ∧ r≤‖z.2‖ ∧ ‖z.2‖<R then μ z.1 z.2 else 0) (P.prod volume) := by
  apply compact_random_field_integrable (P:=P) (f:=fun o x => if bad o ∧ r≤‖x‖ ∧ ‖x‖<R then μ o x else 0) (R:=R)
    (hm.ite ((hb.preimage measurable_fst).inter
      ((measurableSet_le measurable_const (continuous_norm.measurable.comp measurable_snd)).inter
      (measurableSet_lt (continuous_norm.measurable.comp measurable_snd) measurable_const))) measurable_const)
  · intro D; obtain ⟨C,hC⟩ := hbm D
    refine ⟨max C 0,fun o x hx => ?_⟩
    split_ifs
    · exact (hC o x hx).trans (le_max_left _ _)
    · simpa only [abs_zero] using le_max_right C 0
  · exact Eventually.of_forall (fun o x hx => ite_eq_right (fun h => (not_lt.mpr hx) h.2.2))

lemma propagationStepError_total (hm : Measurable (Function.uncurry μ))
    (hb : MeasurableSet {o | bad o})
    (hbm : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |μ o x|≤C)
    (hip : Integrable (Function.uncurry p) (P.prod volume)) :
    (∫ o,(∫ x,propagationStepError (bad o) r R ‖x‖ (μ o x) (p o x)) ∂P)=
      (∫ o,(∫ x,p o x) ∂P)+(∫ o in {o | bad o},∫ x in {x : Position | r≤‖x‖ ∧ ‖x‖<R},μ o x ∂volume ∂P) := by
  let f := fun o x => if bad o ∧ r≤‖x‖ ∧ ‖x‖<R then μ o x else 0
  have hi := shell_error_product_integrable (P:=P) (r:=r) (R:=R) hm hb hbm
  have he : ∀ o,(∫ x,f o x)={o | bad o}.indicator
      (fun o => ∫ x in {x : Position | r≤‖x‖ ∧ ‖x‖<R},μ o x) o := by
    intro o
    by_cases ho : bad o
    · rw [Set.indicator_of_mem (s:={o | bad o}) ho]
      have hS : MeasurableSet {x : Position | r≤‖x‖ ∧ ‖x‖<R} :=
        (measurableSet_le measurable_const continuous_norm.measurable).inter
          (measurableSet_lt continuous_norm.measurable measurable_const)
      rw [←integral_indicator hS]
      apply integral_congr_ae (Eventually.of_forall (fun x => ?_))
      simp only [f,ho,true_and,Set.indicator_apply,mem_ofPred_eq]
    · simp only [f,ho,false_and,ite_false,integral_zero,Set.indicator_of_notMem (s:={o | bad o}) ho]
  change (∫ o,(∫ x,p o x+f o x) ∂P)=_
  have hie : Integrable (Function.uncurry f) (P.prod volume) := hi
  have hiadd : Integrable (fun z : Ω×Position => p z.1 z.2+f z.1 z.2) (P.prod volume) := hip.add hie
  rw [←integral_prod _ hiadd]
  change (∫ z,(Function.uncurry p z + Function.uncurry f z) ∂P.prod volume)=_
  rw [integral_add hip hie,integral_prod _ hip,integral_prod _ hie]
  congr 1
  change (∫ o,(∫ x,f o x) ∂P)=_
  simp_rw [he]
  exact integral_indicator hb

omit [IsProbabilityMeasure P] in
lemma initialPropagationError_total (_ : Measurable (Function.uncurry μ))
    (hb : MeasurableSet {o | bad o}) :
    (∫ o,(∫ x,initialPropagationError (bad o) r (μ o) x) ∂P)=
      ∫ o in {o | bad o},∫ x in Metric.ball (0:Position) r,μ o x ∂volume ∂P := by
  rw [←integral_indicator hb]
  apply integral_congr_ae (Eventually.of_forall (fun o => ?_))
  by_cases ho : bad o
  · rw [Set.indicator_of_mem (s:={o | bad o}) ho,←integral_indicator measurableSet_ball]
    apply integral_congr_ae (Eventually.of_forall (fun x => ?_))
    simp [initialPropagationError,ho,Set.indicator_apply,Metric.mem_ball]
  · simp [initialPropagationError,ho]
end Error
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PropagationPosteriorMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
section Step
variable {Ω A : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace A]
variable {P : Measure Ω} [IsProbabilityMeasure P] {B C r R Z L l1 l2 e ξ hl hh : ℝ}
variable {μ μ' H : Ω → Position → ℝ} {bad : Ω → Prop}
lemma PropagationDatum.posteriorStep_total (d : PropagationDatum P B C r Z L μ)
    (obs : Ω → A) (ho : Measurable obs) (hR : 0<R)
    (hb : MeasurableSet {o | bad o})
    (hH : Measurable (Function.uncurry H)) (hμ : Measurable (Function.uncurry μ))
    (hbH : ∀ D : ℝ,∃ A : ℝ,∀ o x,x∈Metric.closedBall 0 D → |H o x|≤A)
    (hbμ : ∀ D : ℝ,∃ A : ℝ,∀ o x,x∈Metric.closedBall 0 D → |μ o x|≤A)
    (hstep : ∀ᵐ o ∂P,PropagationStepHypotheses (bad o) B C r R Z L l1 l2 e ξ hl hh
      (d.offset o) (H o) (μ o) (d.error o))
    (htower : ∀ᵐ o ∂P,posteriorAverage P obs μ (obs o)=μ' o) :
    let d' := d.posteriorStep obs ho hR hb hH hμ hbH hbμ hstep htower
    (∫ o,(∫ x,d'.error o x) ∂P)=(∫ o,(∫ x,d.error o x) ∂P)+
      (∫ o in {o | bad o},∫ x in {x : Position | r≤‖x‖ ∧ ‖x‖<R},μ o x ∂volume ∂P) := by
  dsimp only
  let q := fun o x => propagationStepError (bad o) r R ‖x‖ (μ o x) (d.error o x)
  change (∫ o,(∫ x,posteriorAverage P obs q (obs o) x) ∂P)=_
  have hq := propagationStepError_joint_measurable (r:=r) (R:=R) hb hμ d.error_measurable
  have hqb := propagationStepError_uniform_bounds (bad:=bad) (r:=r) (R:=R) hbμ d.error_bounds
  have hqs : ∀ᵐ o ∂P,∀ x,R≤‖x‖ → q o x=0 := by
    filter_upwards [d.invariant,hstep] with o hi hs
    exact (hs.next_invariant hi.error_support).error_support
  rw [posteriorAverage_total_integral (f:=q) (P:=P) obs ho hq hqb hqs]
  exact propagationStepError_total hμ hb hbμ d.error_product_integrable
end Step
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PosteriorRegularBounds
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
section Fields
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] {n : ℕ}
variable (P : Measure Ω) [IsFiniteMeasure P] (raw : Ω → Configuration n) (obs : Ω → A)
variable {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g)
variable (hm : (∫ z,g z^2)=1) {c r s : ℝ} (hc : 0 < c) (hr : 0 < r) (hs : 0 < s)

include hg hgs hc hr hs
lemma conditionalPacketDensity_uniform_bounds :
    ∀ D : ℝ,∃ C : ℝ,∀ a x,x∈Metric.closedBall 0 D →
      |conditionalPacketDensity P raw obs g c r s a x|≤C := by
  obtain ⟨C,hC,hCb⟩ := conditionalPacketDensity_bounded P raw obs hg hgs hc hr hs
  exact fun D => ⟨C,fun a x _ => by
    rw [abs_of_nonneg (conditionalPacketDensity_nonneg P raw obs g hc hr hs a x)]
    exact hCb a x⟩

include hm
lemma conditionalPacketPotential_bounded : ∃ C : ℝ,0≤C ∧ ∀ a x,
    |potentialOf (conditionalPacketDensity P raw obs g c r s a) x|≤C := by
  obtain ⟨A,hA,hAb⟩ := conditionalPacketDensity_bounded P raw obs hg hgs hc hr hs
  refine ⟨A*kernelBallMass 1+n,add_nonneg (mul_nonneg hA (kernelBallMass_nonneg 1)) (Nat.cast_nonneg n),fun a x => ?_⟩
  rw [abs_of_nonneg (potentialOf_nonneg (conditionalPacketDensity_nonneg P raw obs g hc hr hs a) x)]
  have H := (potential_integrable_and_bound (x:=x) (mixturePacketDensity_integrable hg hm hc hr hs _)
    (conditionalPacketDensity_nonneg P raw obs g hc hr hs a) (by norm_num : (0:ℝ)<1)
    (fun y _ => hAb a y)).2
  change potentialOf (conditionalPacketDensity P raw obs g c r s a) x ≤
    A*kernelBallMass 1+1⁻¹*(∫ y,conditionalPacketDensity P raw obs g c r s a y) at H
  simpa only [inv_one,one_mul,conditionalPacketDensity_mass P raw obs hg hm hc hr hs] using H

lemma conditionalPacketOffset_uniform_bounds :
    ∀ D : ℝ,∃ C : ℝ,∀ a x,x∈Metric.closedBall 0 D →
      |-potentialOf (conditionalPacketDensity P raw obs g c r s a) x|≤C := by
  obtain ⟨C,hC,hCb⟩ := conditionalPacketPotential_bounded P raw obs hg hgs hm hc hr hs
  exact fun D => ⟨C,fun a x _ => by simpa only [abs_neg] using hCb a x⟩
end Fields
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PosteriorPropagationData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

lemma posterior_nuclear_datum {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (raw : Ω → Configuration n) (obs : Ω → A) (ho : Measurable obs)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g) (hm : (∫ z,g z^2)=1)
    {c r s : ℝ} (hc : 0 < c) (hr : 0 < r) (hs : 0 < s) (Z : ℝ) :
    let μ := fun o => conditionalPacketDensity P raw obs g c r s (obs o)
    NuclearRandomDatum Z μ (fun o x => -potentialOf (μ o) x) := by
  let μ := fun o => conditionalPacketDensity P raw obs g c r s (obs o)
  refine ⟨(measurable_conditionalPacketDensity_joint P raw obs hg hgs hc hr hs).comp (ho.prodMap measurable_id),
    ((measurable_conditionalPacketPotential_joint P raw obs hg hgs hm hc hr hs).comp (ho.prodMap measurable_id)).neg,
    ?_,?_,fun o => (conditionalPacketPotential_continuous P raw obs hg hgs hm hc hr hs (obs o)).neg,
    fun o x => neg_nonpos.mpr (potentialOf_nonneg (conditionalPacketDensity_nonneg P raw obs g hc hr hs (obs o)) x),
    fun o => conditionalPacketDensity_nonneg P raw obs g hc hr hs (obs o),
    fun o => mixturePacketDensity_integrable hg hm hc hr hs _,fun o => ?_⟩
  · intro D
    obtain ⟨C,hC⟩ := conditionalPacketDensity_uniform_bounds P raw obs hg hgs hc hr hs D
    exact ⟨C,fun o => hC (obs o)⟩
  · intro D
    obtain ⟨C,hC⟩ := conditionalPacketOffset_uniform_bounds P raw obs hg hgs hm hc hr hs D
    exact ⟨C,fun o => hC (obs o)⟩
  · exact conditionalPacketField_nuclear P raw obs hg hgs hm hc hr hs (obs o) Z

section Assembly
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B C r Z : ℝ}
variable {μ H : Ω → Position → ℝ} {bad : Ω → Prop}

lemma PropagationDatum.step_hypotheses (k : PropagationConstants B C)
    (d : PropagationDatum P B C r Z k.L μ) (q : NuclearRandomDatum Z μ H)
    (hB : 0<B) (hBC : B≤C) (hr : 0 < r) (hbar : 4*Real.pi*kTF*Real.sqrt B≤19/2)
    (hcap : ∀ o,¬bad o → ∀ x,r≤‖x‖ → ‖x‖≤4*k.L*r → Z*coulombKernel x+H o x≤C/‖x‖^4)
    (hinv : ∀ o,¬bad o → ∀ x,r≤‖x‖ → ‖x‖≤4*k.L*r → ∀ h∈Icc (B/2) C,
      (Coulomb.tfScalarDensity h≤‖x‖^6*μ o x → h-k.ξ≤‖x‖^4*(Z*coulombKernel x+H o x)) ∧
      (‖x‖^6*μ o x≤Coulomb.tfScalarDensity h → ‖x‖^4*(Z*coulombKernel x+H o x)≤h+k.ξ)) :
    ∀ᵐ o ∂P,PropagationStepHypotheses (bad o) B C r (2*r) Z k.L k.l1 k.l2 k.e k.ξ (B/2) C
      (d.offset o) (H o) (μ o) (d.error o) := by
  filter_upwards [d.invariant] with o hi
  refine ⟨hB,hr,rfl,k.L_large,k.l2_pos.le,k.l2_le_l1,k.l1_le_gamma,hBC,k.upper_overlap,
    k.e_pos,k.xi_pos.le,k.xi_lt_l2,k.gain_gap,k.height_lower,le_rfl,
    hi.continuous_offset,q.continuous_H o,q.nonnegative_mu o,hi.nonnegative_error,
    q.mu_measurable.of_uncurry_left,d.error_measurable.of_uncurry_left,?_,?_,
    hi.weak,q.nuclear o,hbar,hi.caps,?_,?_⟩
  · intro D; obtain ⟨M,hM⟩ := q.mu_bounds D; exact ⟨M,hM o⟩
  · intro D; obtain ⟨M,hM⟩ := d.error_bounds D; exact ⟨M,hM o⟩
  · intro hb x hx hx'; apply hcap o hb x hx; nlinarith only [hx']
  · intro hb x hx hx' h hh
    exact (hinv o hb x hx (by nlinarith only [hx']) h hh).symm

lemma NuclearRandomDatum.initial_hypotheses (q : NuclearRandomDatum Z μ H)
    {a L : ℝ} (hB : 0<B) (hZ : 0≤Z) (hr : 0 < r) (ha : 0≤a) (hL : 2≤L)
    (hBZ : B≤(1/10:ℝ)*Z*r^3) (hBC : B≤C) (hZC : 32*Z*r^3≤C)
    (hquad : 4*a*r^2≤(1/20:ℝ)*Z/r) (hreac : tfReaction (2*Z/r)≤6*a)
    (hbar : 4*Real.pi*kTF*Real.sqrt B≤19/2)
    (hlo : ∀ o,¬bad o → ∀ x,r≤‖x‖ → ‖x‖≤2*r → -(1/10:ℝ)*Z/r≤H o x) :
    ∀ o,InitialPropagationData (bad o) B C Z r a L (H o) (μ o) := by
  intro o
  refine ⟨hB,hZ,hr,ha,hL,hBZ,hBC,hZC,hquad,hreac,hbar,q.continuous_H o,
    q.nonpositive_H o,hlo o,q.mu_measurable.of_uncurry_left,q.nonnegative_mu o,?_,q.nuclear o⟩
  intro D
  obtain ⟨M,hM⟩ := q.mu_bounds D
  exact ⟨M,hM o⟩
end Assembly
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
section Iteration
variable {Ω A : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace A]
variable {P : Measure Ω} [IsProbabilityMeasure P] {B C r Z : ℝ}

theorem propagation_finite_iteration (k : PropagationConstants B C)
    (hB : 0<B) (hBC : B≤C) (hr : 0 < r) (hbar : 4*Real.pi*kTF*Real.sqrt B≤19/2)
    (J : ℕ) (μ H : ℕ → Ω → Position → ℝ) (obs : ℕ → Ω → A) (bad : ℕ → Ω → Prop)
    (d₀ : PropagationDatum P B C r Z k.L (μ 0))
    {M₀ M : ℝ} (hM₀ : 0≤M₀) (hM : 0≤M)
    (hinit : (∫ o,(∫ x,d₀.error o x) ∂P)≤M₀*r^9)
    (ho : ∀ j<J,Measurable (obs (j+1)))
    (hb : ∀ j<J,MeasurableSet {o | bad j o})
    (hq : ∀ j<J,NuclearRandomDatum Z (μ j) (H j))
    (hcap : ∀ j<J,∀ o,¬bad j o → ∀ x,r*2^j≤‖x‖ → ‖x‖≤4*k.L*(r*2^j) →
      Z*coulombKernel x+H j o x≤C/‖x‖^4)
    (hinv : ∀ j<J,∀ o,¬bad j o → ∀ x,r*2^j≤‖x‖ → ‖x‖≤4*k.L*(r*2^j) → ∀ h∈Icc (B/2) C,
      (Coulomb.tfScalarDensity h≤‖x‖^6*μ j o x → h-k.ξ≤‖x‖^4*(Z*coulombKernel x+H j o x)) ∧
      (‖x‖^6*μ j o x≤Coulomb.tfScalarDensity h → ‖x‖^4*(Z*coulombKernel x+H j o x)≤h+k.ξ))
    (htower : ∀ j<J,∀ᵐ o ∂P,posteriorAverage P (obs (j+1)) (μ j) (obs (j+1) o)=μ (j+1) o)
    (hcost : ∀ j<J,(∫ o in {o | bad j o},∫ x in {x : Position | r*2^j≤‖x‖ ∧ ‖x‖<2*(r*2^j)},
      μ j o x ∂volume ∂P)≤M*(r*2^j)^9) :
    ∃ d : PropagationDatum P B C (r*2^J) Z k.L (μ J),
      (∫ o,(∫ x,d.error o x) ∂P)≤(M₀+M)*(r*2^J)^9 := by
  have HI : ∀ j≤J,∃ d : PropagationDatum P B C (r*2^j) Z k.L (μ j),
      (∫ o,(∫ x,d.error o x) ∂P)≤(M₀+M)*(r*2^j)^9 := by
    intro j
    induction j with
    | zero =>
      intro hj
      have he : r*(2:ℝ)^(0:ℕ)=r := by simp
      rw [he]
      exact ⟨d₀,hinit.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hM) (by positivity))⟩
    | succ j ih =>
      intro hj
      have hjJ : j<J := Nat.lt_of_succ_le hj
      obtain ⟨d,hd⟩ := ih (Nat.le_of_lt hjJ)
      have hrj : 0 < r*2^j := by positivity
      have hs := d.step_hypotheses k (hq j hjJ) hB hBC hrj hbar (hcap j hjJ) (hinv j hjJ)
      let d' := d.posteriorStep (obs (j+1)) (ho j hjJ) (by positivity : 0<2*(r*2^j))
        (hb j hjJ) (hq j hjJ).H_measurable (hq j hjJ).mu_measurable
        (hq j hjJ).H_bounds (hq j hjJ).mu_bounds hs (htower j hjJ)
      have htotal := d.posteriorStep_total (obs (j+1)) (ho j hjJ) (by positivity : 0<2*(r*2^j))
        (hb j hjJ) (hq j hjJ).H_measurable (hq j hjJ).mu_measurable
        (hq j hjJ).H_bounds (hq j hjJ).mu_bounds hs (htower j hjJ)
      have he : r*2^(j+1)=2*(r*2^j) := by rw [pow_succ]; ring
      rw [he]
      refine ⟨d',?_⟩
      change (∫ o,(∫ x,d'.error o x) ∂P)=_ at htotal
      rw [htotal]
      calc
        _≤(M₀+M)*(r*2^j)^9+M*(r*2^j)^9 := add_le_add hd (hcost j hjJ)
        _≤(M₀+M)*(2*(r*2^j))^9 := by
          rw [mul_pow]
          nlinarith [pow_nonneg hrj.le 9]
  exact HI J le_rfl
end Iteration
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_CountTestFlux
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

lemma countTest_laplacian_scaled (R : ℝ) (x : Position) :
    coordinateLaplacian (Coulomb.countTest 0 R) x=
      R⁻¹^2*coordinateLaplacian Coulomb.cutSeed (R⁻¹ • x) := by
  unfold Coulomb.countTest
  rw [Coulomb.coordinateLaplacian_scaled (Coulomb.cutSeed_smooth.of_le (WithTop.coe_le_coe.mpr le_top))]
  simp only [sub_zero]

lemma countTest_laplacian_inner {R : ℝ} {x : Position} (hx : ‖x‖<R) :
    coordinateLaplacian (Coulomb.countTest 0 R) x=0 := by
  have hR := (norm_nonneg x).trans_lt hx
  have he : Coulomb.countTest 0 R=ᶠ[𝓝 x] (fun _ : Position => (1:ℝ)) := by
    filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds hx)] with y hy
    exact Coulomb.countTest_one 0 hR (by simpa only [sub_zero] using hy.le)
  rw [coordinateLaplacian_congr_nhds he]
  simp [coordinateLaplacian]

lemma countTest_laplacian_abs_integral {R : ℝ} (hR : 0<R) :
    (∫ x,|coordinateLaplacian (Coulomb.countTest 0 R) x|)=
      R*(∫ x,|coordinateLaplacian Coulomb.cutSeed x|) := by
  simp only [countTest_laplacian_scaled,abs_mul,abs_of_nonneg (sq_nonneg R⁻¹),integral_const_mul]
  rw [Measure.integral_comp_inv_smul volume (fun x => |coordinateLaplacian Coulomb.cutSeed x|) R]
  simp only [show Module.finrank ℝ Position=3 by simp [Position],smul_eq_mul,abs_of_pos (pow_pos hR 3)]
  field_simp

lemma countTest_pairing_bound {F : Position → ℝ} {C R : ℝ}
    (hF : Measurable F) (hC : 0≤C) (hR : 0<R)
    (hbound : ∀ x,R≤‖x‖ → |F x|≤C/‖x‖^4) :
    |∫ x,F x*coordinateLaplacian (Coulomb.countTest 0 R) x|≤
      C*(∫ x,|coordinateLaplacian Coulomb.cutSeed x|)/R^3 := by
  let Δ : Position → ℝ := coordinateLaplacian (Coulomb.countTest 0 R)
  have hΔc : Continuous Δ := (contDiff_coordinateLaplacian (Coulomb.countTest_smooth 0 R)).continuous
  have hΔs : HasCompactSupport Δ := hasCompactSupport_coordinateLaplacian (Coulomb.countTest_compact 0 hR)
  have hiΔ : Integrable (fun x => |Δ x|) := (hΔc.integrable_of_hasCompactSupport hΔs).abs
  have hb : ∀ x,|F x*Δ x|≤(C/R^4)*|Δ x| := by
    intro x
    by_cases hx : R≤‖x‖
    · rw [abs_mul]
      apply mul_le_mul_of_nonneg_right ((hbound x hx).trans ?_) (abs_nonneg _)
      exact div_le_div_of_nonneg_left hC (pow_pos hR 4) (pow_le_pow_left₀ hR.le hx 4)
    · rw [show Δ x=0 from countTest_laplacian_inner (lt_of_not_ge hx)]
      simp
  have hi : Integrable (fun x => F x*Δ x) :=
    (hiΔ.const_mul (C/R^4)).mono' (hF.mul hΔc.measurable).aestronglyMeasurable
      (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x))
  calc
    _≤∫ x,|F x*Δ x| := abs_integral_le_integral_abs
    _≤∫ x,(C/R^4)*|Δ x| := integral_mono hi.abs (hiΔ.const_mul _) hb
    _=(C/R^4)*(R*(∫ x,|coordinateLaplacian Coulomb.cutSeed x|)) := by
      rw [integral_const_mul,countTest_laplacian_abs_integral hR]
    _=_ := by field_simp

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PropagationMassTest
attribute [-instance] _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

lemma PropagationInvariant.mass_test {B C r Z L : ℝ} {u μ p : Position → ℝ}
    (d : PropagationInvariant B C r Z L u μ p) (hr : 0 < r)
    (hμ : Integrable μ) (hp : Integrable p)
    {φ : Position → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφn : ∀ x,0≤φ x) (hone : ∀ x,‖x‖ ≤ r → φ x=1) :
    (∫ x,cutoffReaction r (fun y => Z*coulombKernel y+u y) x*φ x) ≤
      4*Real.pi*(Z-(∫ x in Metric.ball 0 r,μ x)+(∫ x,p x))+
        (∫ x,(Z*coulombKernel x+u x)*coordinateLaplacian φ x) := by
  let m : Position → ℝ := (Metric.ball (0:Position) r).indicator μ
  have him : Integrable m := hμ.indicator measurableSet_ball
  have hmp : ∀ x,m x*φ x=m x := by
    intro x
    by_cases hx : ‖x‖ < r
    · simp only [m,Set.indicator_of_mem (show x∈Metric.ball (0:Position) r by simpa using hx),hone x hx.le,mul_one]
    · simp [m,show x∉Metric.ball (0:Position) r by simpa using hx]
  have hpp : ∀ x,p x*φ x=p x := by
    intro x
    by_cases hx : ‖x‖ < r
    · rw [hone x hx.le,mul_one]
    · rw [d.error_support x (le_of_not_gt hx),zero_mul]
  have hic := integrable_mul_test_on
    ((cutoffReaction_offset_locallyIntegrable (Z:=Z) hr d.continuous_offset).locallyIntegrableOn univ)
    hφ.continuous hc (subset_univ _)
  have he : (fun x => propagationRHS r ‖x‖ (μ x) (p x) (Z*coulombKernel x+u x)*φ x)=
      fun x => 4*Real.pi*(m x-p x)+cutoffReaction r (fun y => Z*coulombKernel y+u y) x*φ x := by
    funext x
    rw [propagationRHS_eq,add_mul,propagationCoreSource,mul_assoc,sub_mul,hpp]
    have hh : (if ‖x‖ < r then μ x else 0)=m x := by
      simp only [m,Set.indicator,Metric.mem_ball,dist_zero_right]
    rw [hh,hmp]
  have hicore : Integrable (fun x => 4*Real.pi*(m x-p x)) := (him.sub hp).const_mul (4*Real.pi)
  have H := d.weak φ hφ hc (subset_univ _) hφn
  rw [hone 0 (by simpa using hr.le),he,
    integral_add hicore hic,
    integral_const_mul,integral_sub him hp] at H
  have hm : (∫ x,m x)=∫ x in Metric.ball 0 r,μ x := integral_indicator measurableSet_ball
  rw [hm] at H
  linarith only [H]

end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

lemma propagation_shell_volume {r : ℝ} (hr : 0 < r) :
    (volume : Measure Position).real (Metric.ball 0 (2*r) \ Metric.ball 0 r)=
      (28*Real.pi/3)*r^3 := by
  rw [measureReal_sdiff (Metric.ball_subset_ball (by linarith)) measurableSet_ball,
    Coulomb.volume_real_ball_three _ (by positivity),Coulomb.volume_real_ball_three _ hr.le]
  ring

lemma propagationBarrier_shell_lower {B r : ℝ} (hB : 0≤B) (hr : 0 < r)
    {x : Position} (hx : r≤‖x‖) (hx' : ‖x‖≤2*r) :
    (7*B/128)/r^4≤propagationBarrier B r x := by
  have hd := hr.trans_le hx
  calc
    _=((7/8:ℝ)*B)/(2*r)^4 := by ring
    _≤((7/8:ℝ)*B)/‖x‖^4 := div_le_div_of_nonneg_left (by positivity)
      (pow_pos hd 4) (pow_le_pow_left₀ hd.le hx' 4)
    _≤_ := (propagationBarrier_two_sided hB hr hx).1

lemma PropagationInvariant.reaction_shell_test {B C r Z L R : ℝ} {u μ p : Position → ℝ}
    (d : PropagationInvariant B C r Z L u μ p) (hr : 0 < r) (hB : 0≤B)
    (hR : 2*r≤R) :
    (tfReaction (7*B/128)*(28*Real.pi/3))/r^3≤
      ∫ x,cutoffReaction r (fun y => Z*coulombKernel y+u y) x*Coulomb.countTest 0 R x := by
  let F := fun x => cutoffReaction r (fun y => Z*coulombKernel y+u y) x*Coulomb.countTest 0 R x
  let A : Set Position := Metric.ball 0 (2*r) \ Metric.ball 0 r
  have hRp : 0<R := (by positivity : (0:ℝ)<2*r).trans_le hR
  have hi : Integrable F := integrable_mul_test_on
    ((cutoffReaction_offset_locallyIntegrable (Z:=Z) hr d.continuous_offset).locallyIntegrableOn univ)
    (Coulomb.countTest_smooth 0 R).continuous (Coulomb.countTest_compact 0 hRp) (subset_univ _)
  have hn : ∀ x,0≤F x := by
    intro x
    apply mul_nonneg _ (Coulomb.countTest_nonneg 0 R x)
    unfold cutoffReaction Set.indicator
    split_ifs
    · exact tfReaction_nonneg _
    · exact le_rfl
  have hAf : volume A<⊤ := lt_of_le_of_lt (measure_mono sdiff_subset) Metric.isBounded_ball.measure_lt_top
  have : IsFiniteMeasure (volume.restrict A) := ⟨by simpa using hAf⟩
  have hb : ∀ x∈A,tfReaction (7*B/128)/r^6≤F x := by
    intro x hx
    have hl : r≤‖x‖ := le_of_not_gt (by simpa using hx.2)
    have hu : ‖x‖<2*r := by simpa using hx.1
    have Hone := Coulomb.countTest_one (0:Position) hRp
      (show ‖x-0‖≤R by simpa using hu.le.trans hR)
    change _ ≤ cutoffReaction r (fun y => Z*coulombKernel y+u y) x*Coulomb.countTest 0 R x
    rw [Hone,mul_one]
    simp only [cutoffReaction,Set.indicator_of_mem (show x∈{x : Position | r≤‖x‖} from hl)]
    rw [←tfReaction_div_fourth _ hr]
    exact tfReaction_monotone ((propagationBarrier_shell_lower hB hr hl hu.le).trans (d.caps x hl).1)
  have H := integral_mono_ae (integrable_const (tfReaction (7*B/128)/r^6)) hi.integrableOn
    (ae_restrict_of_forall_mem (measurableSet_ball.diff measurableSet_ball) hb)
  rw [setIntegral_const] at H
  have Hvol : (volume : Measure Position).real A=(28*Real.pi/3)*r^3 := propagation_shell_volume hr
  rw [Hvol,smul_eq_mul] at H
  have he : (28*Real.pi/3)*r^3*(tfReaction (7*B/128)/r^6)=
      (tfReaction (7*B/128)*(28*Real.pi/3))/r^3 := by field_simp
  rw [he] at H
  exact H.trans (setIntegral_le_integral hi (Eventually.of_forall hn))

theorem PropagationInvariant.charge_deficit {B C r Z L : ℝ} {u μ p : Position → ℝ}
    (d : PropagationInvariant B C r Z L u μ p) (hr : 0 < r) (hB : 0≤B) (hC : 0≤C)
    (hμ : Integrable μ) (hp : Integrable p) :
    (tfReaction (7*B/128)*(28*Real.pi/3))/(4*Real.pi*r^3)≤
      Z-(∫ x in Metric.ball 0 r,μ x)+(∫ x,p x) := by
  let D := Z-(∫ x in Metric.ball 0 r,μ x)+(∫ x,p x)
  let I := ∫ x,|coordinateLaplacian Coulomb.cutSeed x|
  have he : ∀ᶠ R : ℝ in atTop,
      (tfReaction (7*B/128)*(28*Real.pi/3))/r^3≤4*Real.pi*D+C*I/R^3 := by
    filter_upwards [eventually_ge_atTop (2*r)] with R hR
    have hRp : 0<R := (by positivity : (0:ℝ)<2*r).trans_le hR
    have hrR : r≤R := (by linarith : r≤2*r).trans hR
    have h1 := d.reaction_shell_test hr hB hR
    have h2 := d.mass_test hr hμ hp (Coulomb.countTest_smooth 0 R) (Coulomb.countTest_compact 0 hRp)
      (Coulomb.countTest_nonneg 0 R) (fun x hx => Coulomb.countTest_one 0 hRp (by simpa using hx.trans hrR))
    have h3 := countTest_pairing_bound (F:=fun x => Z*coulombKernel x+u x)
      ((measurable_const.mul measurable_coulombKernel).add d.continuous_offset.measurable) hC hRp
      (fun x hx => by
        have H := d.caps x (hrR.trans hx)
        rw [abs_of_nonneg (((by positivity : (0:ℝ)≤(7/8:ℝ)*B/‖x‖^4).trans
          (propagationBarrier_two_sided hB hr (hrR.trans hx)).1).trans H.1)]
        exact H.2)
    exact h1.trans (h2.trans (add_le_add le_rfl ((le_abs_self _).trans h3)))
  have ht : Tendsto (fun R : ℝ => 4*Real.pi*D+C*I/R^3) atTop (𝓝 (4*Real.pi*D)) := by
    have H : Tendsto (fun R : ℝ => R⁻¹^3) atTop (𝓝 (0:ℝ)) := by simpa using (tendsto_inv_atTop_zero (𝕜:=ℝ)).pow 3
    convert (tendsto_const_nhds (x:=C*I)).mul H |>.const_add (4*Real.pi*D) using 1 <;>
      simp [div_eq_mul_inv,inv_pow]
  have H := ge_of_tendsto ht he
  apply (div_le_iff₀ (by positivity : 0<4*Real.pi*r^3)).mpr
  have HH := (div_le_iff₀ (pow_pos hr 3)).mp H
  nlinarith only [HH]

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PropagationExpectedDeficit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology Classical
noncomputable section
namespace NeutralAtom
section Expectation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {B C r Z L : ℝ} {μ H : Ω → Position → ℝ}
lemma NuclearRandomDatum.ball_product_integrable (q : NuclearRandomDatum Z μ H) (R : ℝ) :
    Integrable (fun z : Ω×Position => (Metric.ball (0:Position) R).indicator (μ z.1) z.2) (P.prod volume) := by
  apply compact_random_field_integrable (P:=P) (R:=R) (f:=fun o x => (Metric.ball (0:Position) R).indicator (μ o) x)
  · exact q.mu_measurable.indicator (measurableSet_ball.preimage measurable_snd)
  · intro D
    obtain ⟨M,hM⟩ := q.mu_bounds D
    refine ⟨max M 0,?_⟩
    intro o x hx
    by_cases h : x∈Metric.ball (0:Position) R
    · simpa only [Set.indicator_of_mem h] using (hM o x hx).trans (le_max_left M 0)
    · simp only [Set.indicator_of_notMem h,abs_zero]; exact le_max_right M 0
  · exact Eventually.of_forall (fun o x hx => Set.indicator_of_notMem (by simpa using not_lt.mpr hx) _)

theorem PropagationDatum.expected_charge_deficit (d : PropagationDatum P B C r Z L μ)
    (q : NuclearRandomDatum Z μ H) (hr : 0 < r) (hB : 0≤B) (hC : 0≤C) :
    (∫ o,(∫ x in Metric.ball 0 r,μ o x) ∂P)≤
      Z-(tfReaction (7*B/128)*(28*Real.pi/3))/(4*Real.pi*r^3)+
        (∫ o,(∫ x,d.error o x) ∂P) := by
  have hpi := d.error_product_integrable
  have hmi := q.ball_product_integrable (P:=P) r
  have hip : Integrable (fun o => ∫ x,d.error o x) P := hpi.integral_prod_left
  have him : Integrable (fun o => ∫ x in Metric.ball 0 r,μ o x) P := by
    simpa only [integral_indicator measurableSet_ball] using hmi.integral_prod_left
  have H : ∀ᵐ o ∂P,(∫ x in Metric.ball 0 r,μ o x)≤
      Z-(tfReaction (7*B/128)*(28*Real.pi/3))/(4*Real.pi*r^3)+(∫ x,d.error o x) := by
    filter_upwards [d.invariant,hpi.prod_right_ae] with o hi hp
    have HD := hi.charge_deficit hr hB hC (q.integrable_mu o) hp
    linarith only [HD]
  have HH := integral_mono_ae him ((integrable_const _).add hip) H
  change (∫ o,(∫ x in Metric.ball 0 r,μ o x) ∂P)≤
    ∫ o,(Z-(tfReaction (7*B/128)*(28*Real.pi/3))/(4*Real.pi*r^3)+(∫ x,d.error o x)) ∂P at HH
  rw [integral_add (integrable_const _) hip,integral_const,probReal_univ,one_smul] at HH
  exact HH
end Expectation
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology Classical
noncomputable section
namespace NeutralAtom
section Init
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {Z r n ε : ℝ} {μ H : Ω → Position → ℝ} {bad : Ω → Prop}
lemma NuclearRandomDatum.initial_error_bound (q : NuclearRandomDatum Z μ H)
    (hb : MeasurableSet {o | bad o}) (hn : ∀ o,(∫ x,μ o x) ≤ n)
    (hr : 0 < r) (hr1 : r ≤ 1) (hε : 0 ≤ ε) (hnr : n*r^3 ≤ 3*ε^3)
    (hp : P.real {o | bad o} ≤ 343*r^35) :
    (∫ o,(∫ x,initialPropagationError (bad o) r (μ o) x) ∂P) ≤ 1029*ε^3*r^9 := by
  rw [initialPropagationError_total q.mu_measurable hb]
  have hi : Integrable (fun o => ∫ x in Metric.ball 0 r,μ o x) P := by
    simpa only [integral_indicator measurableSet_ball] using (q.ball_product_integrable (P:=P) r).integral_prod_left
  have hno : 0 ≤ n := by
    obtain ⟨o⟩ := nonempty_of_isProbabilityMeasure P
    exact (integral_nonneg (q.nonnegative_mu o)).trans (hn o)
  have H : (∫ o in {o | bad o},∫ x in Metric.ball 0 r,μ o x ∂volume ∂P) ≤ P.real {o | bad o}*n := by
    have HH := integral_mono (hi.integrableOn (s:={o | bad o})) (integrable_const n (μ:=P.restrict {o | bad o}))
      (fun o => (setIntegral_le_integral (q.integrable_mu o)
        (Eventually.of_forall (q.nonnegative_mu o))).trans (hn o))
    simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul] using HH
  calc
    _ ≤ P.real {o | bad o}*n := H
    _ ≤ (343*r^35)*n := mul_le_mul_of_nonneg_right hp hno
    _ = 343*(n*r^3)*r^32 := by ring
    _ ≤ 343*(3*ε^3)*r^32 := by gcongr
    _ = 1029*ε^3*r^32 := by ring
    _ ≤ 1029*ε^3*r^9 := mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one hr.le hr1 (by decide)) (by positivity)
end Init
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

lemma initialAtomicRadius_cubic {ε Z : ℝ} (hZ : 0<Z) :
    Z*(initialAtomicRadius ε Z)^3=ε^3 := by
  rw [initialAtomicRadius,mul_pow,←Real.rpow_mul_natCast hZ.le]
  norm_num
  rw [Real.rpow_neg_one]
  field_simp

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RadialBounds_SpatialAnnulus
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

theorem rawCount_le_packetMass {n : ℕ} (g : Position → ℝ)
    (hg : (∫ y, g y ^ 2) = 1) {c₁ r₀ s : ℝ} (hc : 0 < c₁)
    (hr : 0 < r₀) (hs : 0 < s) (S T : Set Position)
    (hST : ∀ z y, z ∈ S → packetKernel g c₁ r₀ s z y ≠ 0 → y ∈ T)
    (x : Configuration n) : rawCount S x ≤ packetMass g c₁ r₀ s T x := by
  classical
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : x i ∈ S
  · simp only [Set.indicator_of_mem hi]
    have h := setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := T) (μ := volume) (f := packetKernel g c₁ r₀ s (x i)) (fun y hy => by
        by_contra hK
        exact hy (hST (x i) y hi hK))
    rw [h, integral_packetKernel g hg hc hr hs]
  · simp only [Set.indicator_of_notMem hi]
    exact integral_nonneg fun y => packetKernel_nonneg g hc hr hs (x i) y

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PosteriorShellError
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace NeutralAtom
lemma conditional_packet_event_mass {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    {n : ℕ} (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure (Configuration n)) [IsFiniteMeasure ν]
    {raw : Ω → Configuration n} {obs : Ω → A} (hraw : MeasurePreserving raw P ν)
    (ho : Measurable obs) {g : Position → ℝ} (hg : Continuous g) (hm : (∫ y,g y^2)=1)
    {c r₀ s : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀) (hs : 0 < s) (S : Set Position)
    {B : Set Ω} (hB : MeasurableSet[MeasurableSpace.comap obs inferInstance] B) :
    (∫ o in B,∫ y in S,conditionalPacketDensity P raw obs g c r₀ s (obs o) y ∂volume ∂P)=
      ∫ o in B,packetMass g c r₀ s S (raw o) ∂P := by
  have hle : (MeasurableSpace.comap obs inferInstance) ≤ (inferInstance : MeasurableSpace Ω) := ho.comap_le
  have hi := (packetMass_memLp hg hm hc hr₀ hs S ν).integrable (by norm_num)
  calc
    _ = ∫ o in B,(P[fun o => packetMass g c r₀ s S (raw o) | MeasurableSpace.comap obs inferInstance]) o ∂P :=
      integral_congr_ae (ae_restrict_of_ae (conditionalPacketDensity_annulus_eq_condExp P ν hraw ho hg hm hc hr₀ hs S))
    _ = _ := setIntegral_condExp hle (hraw.integrable_comp_of_integrable hi) hB

lemma conditional_packet_event_bound {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    {n : ℕ} (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure (Configuration n)) [IsFiniteMeasure ν]
    {raw : Ω → Configuration n} {obs : Ω → A} (hraw : MeasurePreserving raw P ν)
    (ho : Measurable obs) {g : Position → ℝ} (hg : Continuous g) (hm : (∫ y,g y^2)=1)
    {c r₀ s : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀) (hs : 0 < s) (S T : Set Position)
    (hT : MeasurableSet T)
    (hST : ∀ z y,y∈S → packetKernel g c r₀ s z y≠0 → z∈T)
    {B : Set Ω} (hB : MeasurableSet[MeasurableSpace.comap obs inferInstance] B) :
    (∫ o in B,∫ y in S,conditionalPacketDensity P raw obs g c r₀ s (obs o) y ∂volume ∂P)≤
      Real.sqrt (∫ x,(rawCount T x)^2 ∂ν)*Real.sqrt (P.real B) := by
  rw [conditional_packet_event_mass P ν hraw ho hg hm hc hr₀ hs S hB]
  have hi := (packetMass_memLp hg hm hc hr₀ hs S ν).integrable (by norm_num)
  have hX : MemLp (rawCount (n:=n) T) 2 ν := MemLp.of_bound
    (measurable_rawCount hT).aestronglyMeasurable (n:ℝ) (Eventually.of_forall (fun x => by
      rw [Real.norm_of_nonneg (rawCount_nonneg T x)]; exact rawCount_le_number T x))
  have hY := hX.comp_measurePreserving hraw
  calc
    _ ≤ ∫ o in B,rawCount T (raw o) ∂P := integral_mono
      (hraw.integrable_comp_of_integrable hi).integrableOn
      (hY.integrable (by norm_num)).integrableOn
      (fun o => packetMass_le_rawCount g hm hc hr₀ hs S T hST (raw o))
    _ ≤ Real.sqrt (∫ o,(rawCount T (raw o))^2 ∂P)*Real.sqrt (P.real B) :=
      exceptional_event_bound hY (Eventually.of_forall (fun o => rawCount_nonneg T (raw o))) (ho.comap_le B hB)
    _ = _ := by
      have H := integral_map hraw.measurable.aemeasurable
        (((measurable_rawCount hT).pow_const 2).aestronglyMeasurable :
          AEStronglyMeasurable (fun x : Configuration n => (rawCount T x)^2) (P.map raw))
      rw [hraw.map_eq] at H
      rw [←H]
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_PhysicalInteriorTransfer
attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace NeutralAtom
lemma packet_ball_containment {g : Position → ℝ} (hg : ∀ x,1<‖x‖ → g x=0)
    {c r₀ s R : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀) (hs : 0 < s) (hrR : r₀ ≤ R)
    (hq : c*s^packetExponent ≤ 1/4) {z y : Position}
    (hz : z∈Metric.ball (0:Position) (R/2)) (hK : packetKernel g c r₀ s z y≠0) :
    y∈Metric.ball (0:Position) R := by
  have hR : 0<R := hr₀.trans_le hrR
  have hzn : ‖z‖<R/2 := by simpa using hz
  have hmax : max ‖z‖ r₀ ≤ R := max_le (by linarith) hrR
  have hd := (packetKernel_support g hg hc hr₀ hs z y hK).trans
    ((packetWidth_le c r₀ s hc.le hr₀ hs z).trans
      (mul_le_mul_of_nonneg_left hmax (by positivity)))
  have hq' := mul_le_mul_of_nonneg_right hq hR.le
  have hdiff := norm_sub_norm_le y z
  simp only [Metric.mem_ball,dist_zero_right]
  linarith only [hd,hq',hdiff,hzn,hR]

lemma physical_interior_packet_transfer {n J : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (hn : normSquared ψ=1) (rads : Fin J → ℝ) (j : ℕ)
    {g₀ : Position → ℝ} (hg : Continuous g₀) (hm : (∫ x,g₀ x^2)=1)
    (hgs : ∀ x,1<‖x‖ → g₀ x=0) {c r₀ s R : ℝ}
    (hc : 0 < c) (hr₀ : 0 < r₀) (hs : 0 < s) (hrR : r₀ ≤ R) (hq : c*s^packetExponent ≤ 1/4) :
    letI := rawLaw_isProbability hd.2.2.1 hn
    let P := observationLaw J (rawLaw ψ)
    (∫ x,rawCount (Metric.ball (0:Position) (R/2)) x ∂rawLaw ψ) ≤
      ∫ o,(∫ y in Metric.ball (0:Position) R,
        conditionalPacketDensity P Prod.fst (tailObservation rads j) g₀ c r₀ s (tailObservation rads j o) y) ∂P := by
  have := rawLaw_isProbability hd.2.2.1 hn
  dsimp only
  let P := observationLaw J (rawLaw ψ)
  have hraw := observationLaw_rawProjection (J:=J) (rawLaw ψ)
  have He := conditional_packet_event_mass P (rawLaw ψ) hraw (measurable_tailObservation rads j)
    hg hm hc hr₀ hs (Metric.ball (0:Position) R) (B:=univ) MeasurableSet.univ
  simp only [Measure.restrict_univ] at He
  rw [He]
  have hF : Measurable (rawCount (n:=n) (Metric.ball (0:Position) (R/2))) := measurable_rawCount measurableSet_ball
  have HI := integral_map hraw.measurable.aemeasurable (hF.aestronglyMeasurable (μ:=P.map Prod.fst))
  rw [hraw.map_eq] at HI
  rw [HI]
  apply integral_mono (hraw.integrable_comp_of_integrable ((rawCount_memLp hd.2.2.1 hn measurableSet_ball).integrable (by norm_num)))
    (hraw.integrable_comp_of_integrable ((packetMass_memLp hg hm hc hr₀ hs _ (rawLaw ψ)).integrable (by norm_num)))
  intro o
  exact rawCount_le_packetMass g₀ hm hc hr₀ hs _ _
    (fun z y hz hK => packet_ball_containment hgs hc hr₀ hs hrR hq hz hK) o.1

lemma raw_population_asH1 {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) {S : Set Position} (hS : MeasurableSet S) :
    (∫ x,rawCount S x ∂rawLaw ψ)=
      Coulomb.expectedPopulation (asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1) S := by
  rw [integral_rawLaw hd.2.2.1,rawExpectation_eq_stateWeightedIntegral hd.2.2.1
    (measurable_rawCount hS) (C:=(n:ℝ)) (fun x => by
      rw [Real.norm_of_nonneg (rawCount_nonneg S x)]; exact rawCount_le_number S x)]
  rw [Coulomb.expectedPopulation_eq _ hS]
  change stateWeightedIntegral ψ (fun x => ∑ i : Fin n,S.indicator (fun _ => (1:ℝ)) (x i))=_
  simpa only [Coulomb.potentialForm,Coulomb.localCount,position_flattenConfiguration,rawCount] using
    (asH1_potentialForm ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1 (Coulomb.localCount S)).symm
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_PhysicalFinitePropagation
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

theorem physical_finite_propagation {N J : ℕ} (Z : ℕ) (hZ : 1 ≤ Z)
    {ψ : Wavefunction (N+1)} {g : Gradient (N+1)} (hd : FormDomain ψ g) (hn : normSquared ψ=1)
    {g₀ : 𝓢(Position,ℝ)} (hgs : ∀ x,1<‖x‖ → g₀ x=0) (hm : (∫ x,g₀ x^2)=1)
    {c ε B C r₀ s M : ℝ} (hc : 0 < c) (hε : 0<ε) (hB : 0<B) (hBC : B ≤ C)
    (hr : 0 < r₀) (hr1 : r₀ ≤ 1) (hs : 0 < s) (hM : 0 ≤ M)
    (hq : c*s^packetExponent ≤ 1/4) (hcubic : (Z:ℝ)*r₀^3=ε^3)
    (hnum : (N+1:ℝ) ≤ 3*(Z:ℝ)) (hBe : B ≤ ε^3/10) (heC : 32*ε^3 ≤ C)
    (hR : tfReaction (2*ε^3) ≤ (3/40:ℝ)*ε^3) (hbar : 4*Real.pi*kTF*Real.sqrt B ≤ 19/2)
    (k : PropagationConstants B C) :
    let := rawLaw_isProbability hd.2.2.1 hn
    let P := observationLaw J (rawLaw ψ)
    let rs := fun j : Fin J => r₀*2^j.val
    let μ := fun j o => conditionalPacketDensity P Prod.fst (tailObservation rs j) g₀ c r₀ s (tailObservation rs j o)
    ∀ {G₀ : Set (Fin J → UnorderedArray (N+1))},MeasurableSet G₀ →
      P.real (tailObservation rs 0 ⁻¹' G₀ᶜ) ≤ 343*r₀^35 →
      (∀ a∈G₀,∀ x,r₀ ≤ ‖x‖ → ‖x‖ ≤ 2*r₀ →
        potentialOf (conditionalPacketDensity P Prod.fst (tailObservation rs 0) g₀ c r₀ s a) x ≤ (1/10:ℝ)*(Z:ℝ)/r₀) →
    ∀ (G : Fin J → Set (ObservationSample (N+1) J)),
      (∀ j,MeasurableSet (G j)) →
      (∀ j,∀ o∈G j,∀ x,rs j ≤ ‖x‖ → ‖x‖ ≤ 4*k.L*(rs j) →
        let F := (Z:ℝ)*coulombKernel x-potentialOf (μ j.val o) x
        F ≤ C/‖x‖^4 ∧ ∀ h∈Icc (B/2) C,
          (Coulomb.tfScalarDensity h ≤ ‖x‖^6*μ j.val o x → h-k.ξ ≤ ‖x‖^4*F) ∧
          (‖x‖^6*μ j.val o x ≤ Coulomb.tfScalarDensity h → ‖x‖^4*F ≤ h+k.ξ)) →
      (∀ j,(∫ o in (G j)ᶜ,∫ x in {x : Position | rs j ≤ ‖x‖ ∧ ‖x‖<2*(rs j)},μ j.val o x ∂volume ∂P) ≤ M*(rs j)^9) →
    (∫ x,rawCount (Metric.ball (0:Position) ((r₀*2^J)/2)) x ∂rawLaw ψ) ≤
      (Z:ℝ)-(tfReaction (7*B/128)*(28*Real.pi/3))/(4*Real.pi*(r₀*2^J)^3)+
        (1029*ε^3+M)*(r₀*2^J)^9 := by
  have := rawLaw_isProbability hd.2.2.1 hn
  dsimp only
  let P := observationLaw J (rawLaw ψ)
  let rs := fun j : Fin J => r₀*2^j.val
  let μ := fun j o => conditionalPacketDensity P Prod.fst (tailObservation rs j) g₀ c r₀ s (tailObservation rs j o)
  let H := fun j o x => -potentialOf (μ j o) x
  intro G₀ hG₀ hp₀ hlow G hG hgood hcost
  have hcompact : HasCompactSupport (g₀ : Position → ℝ) := HasCompactSupport.intro
    (isCompact_closedBall (0:Position) 1) (fun x hx => hgs x
      (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hx))
  have hZr : 0<(Z:ℝ) := by exact_mod_cast (zero_lt_one.trans_le hZ)
  have q (j : ℕ) : NuclearRandomDatum (Z:ℝ) (μ j) (H j) :=
    posterior_nuclear_datum P Prod.fst (tailObservation rs j) (measurable_tailObservation rs j)
      g₀.continuous hcompact hm hc hr hs Z
  let bad₀ := fun o => tailObservation rs 0 o∉G₀
  have hb₀ : MeasurableSet {o | bad₀ o} := hG₀.compl.preimage (measurable_tailObservation rs 0)
  have gates := initial_scaled_gates (B:=B) hZr hr hcubic hR
  have init := (q 0).initial_hypotheses (bad:=bad₀) hB hZr.le hr
    (by positivity : 0 ≤ (Z:ℝ)/(80*r₀^3)) k.L_large.le
    (by rw [mul_assoc,hcubic]; linarith only [hBe]) hBC
    (by rw [mul_assoc,hcubic]; exact heC) gates.1 gates.2 hbar (by
      intro o ho x hx hx'
      have hh := hlow (tailObservation rs 0 o) (by simpa only [bad₀,not_not] using ho) x hx hx'
      change potentialOf (μ 0 o) x ≤ _ at hh
      change -(1/10:ℝ)*(Z:ℝ)/r₀ ≤ -potentialOf (μ 0 o) x
      simpa only [neg_mul,neg_div] using neg_le_neg hh)
  let d₀ := initialPropagationDatum (P:=P) hr hb₀ (q 0).H_measurable (q 0).mu_measurable
    (q 0).H_bounds (q 0).mu_bounds (Eventually.of_forall init)
  have hnε : (N+1:ℝ)*r₀^3 ≤ 3*ε^3 := by
    rw [←hcubic,←mul_assoc]
    exact mul_le_mul_of_nonneg_right hnum (pow_nonneg hr.le 3)
  have he₀ : (∫ o,(∫ x,d₀.error o x) ∂P) ≤ 1029*ε^3*r₀^9 :=
    (q 0).initial_error_bound hb₀ (fun o => (conditionalPacketDensity_mass P Prod.fst
      (tailObservation rs 0) g₀.continuous hm hc hr hs _).le) hr hr1 hε.le (by simpa using hnε) hp₀
  let bad := fun j o => ∃ hj : j<J,o∉G ⟨j,hj⟩
  obtain ⟨d,hd'⟩ := propagation_finite_iteration k hB hBC hr hbar J μ H
    (fun j => tailObservation rs j) bad d₀ (by positivity : 0 ≤ 1029*ε^3) hM he₀
    (fun j _ => measurable_tailObservation rs (j+1)) (fun j hj => by
      have he : {o | bad j o}=(G ⟨j,hj⟩)ᶜ := by ext o; simp [bad,hj]
      rw [he]; exact (hG _).compl)
    (fun j _ => q j) (by
      intro j hj o ho x hx hx'
      have hh := (hgood ⟨j,hj⟩ o (by simpa [bad,hj] using ho) x hx hx').1
      simpa only [H,sub_eq_add_neg] using hh) (by
      intro j hj o ho x hx hx' h hh
      have hgood' := (hgood ⟨j,hj⟩ o (by simpa [bad,hj] using ho) x hx hx').2 h hh
      simpa only [H,sub_eq_add_neg] using hgood')
    (fun j _ => posteriorPacketDensity_tower (rawLaw ψ) g₀.continuous hcompact hc hr hs rs (Nat.le_succ j)) (by
      intro j hj
      have he : {o | bad j o}=(G ⟨j,hj⟩)ᶜ := by ext o; simp [bad,hj]
      rw [he]; exact hcost ⟨j,hj⟩)
  have hrJ : 0 < r₀*2^J := by positivity
  have hrle : r₀ ≤ r₀*2^J := le_mul_of_one_le_right hr.le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  have htrans := physical_interior_packet_transfer hd hn rs J g₀.continuous hm hgs hc hr hs hrle hq
  exact htrans.trans ((d.expected_charge_deficit (q J) hrJ hB.le (hB.le.trans hBC)).trans
    (add_le_add le_rfl hd'))
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RadialBounds_PhysicalShellError
attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace NeutralAtom
lemma shell_error_numeric {C K D r m p : ℝ} (hC : 0≤C) (hK : 0≤K) (hD : 0≤D)
    (hr : 0 < r) (hr1 : r≤1) (hDr : D*r^7≤1)
    (hm : m≤C*(Coulomb.screenMass D r)^2) (hp : p≤K*r^24) :
    Real.sqrt m*Real.sqrt p≤2*Real.sqrt C*Real.sqrt K*r^9 := by
  have hM : Real.sqrt m≤2*Real.sqrt C/r^3 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,hm.trans ?_⟩
    have H := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Coulomb.screenMass_pos D r).le (screenMass_small_offset hr hr1 hD hDr) 2) hC
    apply H.trans_eq
    field_simp
    nlinarith [Real.sq_sqrt hC]
  have hP : Real.sqrt p≤Real.sqrt K*r^12 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,hp.trans_eq ?_⟩
    rw [mul_pow,Real.sq_sqrt hK,←pow_mul]
  calc
    _≤(2*Real.sqrt C/r^3)*(Real.sqrt K*r^12) :=
      mul_le_mul hM hP (Real.sqrt_nonneg p) (by positivity)
    _=_ := by field_simp

lemma physical_bad_shell_error : ∃ C : ℝ,0≤C ∧
    ∀ {n J : ℕ} (Z : ℕ) (hZ : 1≤Z) {ψ : Wavefunction n} {g : Gradient n},
    ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
    ∀ {E D : ℝ},(E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g≤E+D → 0≤D →
    ∀ {g₀ : Position → ℝ},Continuous g₀ → (∫ y,g₀ y^2)=1 → (∀ y,1<‖y‖ → g₀ y=0) →
    ∀ {c r₀ s r K : ℝ},0 < c → 0 < r₀ → 0 < s → r₀ ≤ r → r≤1 → D*r^7≤1 →
    c*s^packetExponent≤1/4 → 0≤K →
    ∀ (rads : Fin J → ℝ) (j : ℕ),
    ∀ {Bad : Set (ObservationSample n J)},MeasurableSet[observationSigma rads j] Bad →
    (observationLaw J (rawLaw ψ)).real Bad≤K*r^24 →
    letI := rawLaw_isProbability hd.2.2.1 hn
    let P := observationLaw J (rawLaw ψ)
    (∫ o in Bad,∫ y in {y : Position | r≤‖y‖ ∧ ‖y‖<2*r},
      conditionalPacketDensity P Prod.fst (tailObservation rads j) g₀ c r₀ s (tailObservation rads j o) y ∂volume ∂P)≤
      C*Real.sqrt K*r^9 := by
  obtain ⟨C,hC,HC⟩ := atomic_raw_annular_second_moment (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<4)
  refine ⟨2*Real.sqrt C,by positivity,?_⟩
  intro n J Z hZ ψ g hd hn E D hE he hD g₀ hg hm hgs c r₀ s r K hc hr₀ hs hrr hr1 hDr hq hK rads j Bad hBad hp
  have := rawLaw_isProbability hd.2.2.1 hn
  dsimp only
  have hr : 0 < r := hr₀.trans_le hrr
  have hT : MeasurableSet {y : Position | r/2<‖y‖ ∧ ‖y‖<4*r} :=
    (measurableSet_lt measurable_const continuous_norm.measurable).inter
      (measurableSet_lt continuous_norm.measurable measurable_const)
  have H := conditional_packet_event_bound (observationLaw J (rawLaw ψ)) (rawLaw ψ)
    (observationLaw_rawProjection (J:=J) (rawLaw ψ)) (measurable_tailObservation rads j) hg hm hc hr₀ hs
    {y : Position | r≤‖y‖ ∧ ‖y‖<2*r} {y : Position | r/2<‖y‖ ∧ ‖y‖<4*r} hT
    (fun z y hy hk => packet_shell_center hgs hc hr₀ hs hrr hq hy hk) hBad
  apply H.trans
  apply shell_error_numeric hC hK hD hr hr1 hDr _ hp
  simpa only [one_div_mul_eq_div] using HC Z hZ hd hn hE he hD hr
end NeutralAtom

end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_PhysicalCoreMean
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

lemma dyadic_endpoint {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    ∃ J : ℕ,r*2^J ≤ s ∧ s<2*(r*2^J) ∧ ∀ j ≤ J,r*2^j ≤ s := by
  obtain ⟨J,hJ,hJ'⟩ := exists_nat_pow_near ((le_div_iff₀ hr).mpr (by simpa using hrs)) (by norm_num : (1:ℝ)<2)
  have H : r*2^J ≤ s := by simpa only [mul_comm] using (le_div_iff₀ hr).mp hJ
  refine ⟨J,H,?_,fun j hj => (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hj) hr.le).trans H⟩
  have HH := (div_lt_iff₀ hr).mp hJ'
  rw [pow_succ] at HH
  nlinarith only [HH]

theorem physical_propagated_core_mean : ∃ a M : ℝ,0<a ∧ 0 ≤ M ∧
    ∀ D : ℝ,0 ≤ D → ∃ s₀ : ℝ,0 < s₀ ∧ ∀ s : ℝ,0 < s → s < s₀ →
    ∃ Zmin : ℕ,∀ Z : ℕ,Zmin ≤ Z → ∀ (hZ : 1 ≤ Z) {N : ℕ}
      {ψ : Wavefunction (N+1)} {g : Gradient (N+1)},
    ∀ (hd : FormDomain ψ g) (_ : normSquared ψ=1),
    (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)),FormDomain χ h → normSquared χ=1 →
      energy Z ψ g ≤ energy Z χ h) →
    ∀ {E : ℝ},(E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E+D → (N+1:ℝ) ≤ 3*(Z:ℝ) →
    Coulomb.expectedPopulation (asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1)
      (Metric.ball (0:Position) (s/4)) ≤ (Z:ℝ)-a/s^3+M*s^9 := by
  obtain ⟨εmax,hεmax,HI⟩ := physical_initial_event
  obtain ⟨ε,B,hε,hεceil,hB,hBe,hR,hbar⟩ := initial_constants_exist hεmax
  let C := max physicalSpatialCap (max B (32*ε^3))
  have hBC : B ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hcapC : physicalSpatialCap ≤ C := le_max_left _ _
  have heC : 32*ε^3 ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨k⟩ := propagation_constants_exist hB hBC
  obtain ⟨K,hK,HG⟩ := physical_propagation_good_events Coulomb.unitWindow Coulomb.unitWindow_support
    Coulomb.unitWindow_mass Coulomb.unitWindow_radial (by norm_num : (0:ℝ)<1) hB hBC hcapC k
  obtain ⟨M,hM,HC⟩ := physical_bad_shell_error
  let A := tfReaction (7*B/128)*(28*Real.pi/3)/(4*Real.pi)
  have hA : 0<A := by
    dsimp [A]
    rw [tfReaction_posFactor (by positivity)]
    have hk := kTF_pos
    positivity
  let T := 1029*ε^3+M*Real.sqrt K
  have hT : 0 ≤ T := by dsimp [T]; positivity
  refine ⟨A,T,hA,hT,?_⟩
  intro D hD
  obtain ⟨s₀,hs₀,hs₀1,hgates,HG⟩ := HG D hD
  refine ⟨s₀,hs₀,?_⟩
  intro s hs hss
  have hs1 : s ≤ 1 := hss.le.trans hs₀1
  obtain ⟨hq1,hq2,hDs⟩ := hgates hs hss
  obtain ⟨Zi,Hi⟩ := HI hε hεceil D Coulomb.unitWindow Coulomb.unitWindow_mass
    Coulomb.unitWindow_radial Coulomb.unitWindow_support (by norm_num : (0:ℝ)<1) hs hq1
  have hsmall : ∀ᶠ Z : ℕ in atTop,initialAtomicRadius ε (Z:ℝ) ≤ s :=
    (tendsto_natCast_atTop_atTop.eventually ((initialAtomicRadius_tendsto hε).mono_right nhdsWithin_le_nhds |>.eventually (gt_mem_nhds hs))).mono
      (fun _ h => h.le)
  obtain ⟨Zr,Hr⟩ := eventually_atTop.mp hsmall
  refine ⟨max Zi Zr,?_⟩
  intro Z hZm hZ N ψ g hd hn hmin E hE he hnum
  have hZi : Zi ≤ Z := (le_max_left _ _).trans hZm
  have hZr : Zr ≤ Z := (le_max_right _ _).trans hZm
  have hZpos : 0<(Z:ℝ) := by exact_mod_cast (zero_lt_one.trans_le hZ)
  let r₀ := initialAtomicRadius ε (Z:ℝ)
  have hr : 0 < r₀ := initialAtomicRadius_pos hε hZpos
  have hrs : r₀ ≤ s := Hr Z hZr
  have hr1 : r₀ ≤ 1 := hrs.trans hs1
  obtain ⟨J,hJs,hJs',hjr⟩ := dyadic_endpoint hr hrs
  have := rawLaw_isProbability hd.2.2.1 hn
  let P := observationLaw J (rawLaw ψ)
  let rs := fun j : Fin J => r₀*2^j.val
  have hscale (j : Fin J) : rs j ≤ s := hjr j.val j.isLt.le
  have hge (j : Fin J) : r₀ ≤ rs j := le_mul_of_one_le_right hr.le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  obtain ⟨G₀,hG₀,hp₀,hlo⟩ := Hi Z hZi hZ (J:=J) hd hn hmin hE he hnum
  have HG' := fun j : Fin J => HG Z hZ hd hn hmin hE he hr hs hss j (hscale j)
  choose G hG hp HGood using HG'
  have hcost (j : Fin J) :
      (∫ o in (G j)ᶜ,∫ y in {y : Position | rs j ≤ ‖y‖ ∧ ‖y‖<2*(rs j)},
        conditionalPacketDensity P Prod.fst (tailObservation rs j.val) Coulomb.unitWindow 1 r₀ s
          (tailObservation rs j.val o) y ∂volume ∂P) ≤ M*Real.sqrt K*(rs j)^9 := by
    exact HC Z hZ hd hn hE he hD Coulomb.unitWindow.continuous Coulomb.unitWindow_mass
      Coulomb.unitWindow_support (by norm_num : (0:ℝ)<1) hr hs (hge j) ((hscale j).trans hs1)
      ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hr.trans_le (hge j)).le (hscale j) 7) hD).trans hDs)
      hq2 hK.le rs j.val (hG j).2.compl (hp j)
  have HF := physical_finite_propagation Z hZ hd hn Coulomb.unitWindow_support Coulomb.unitWindow_mass
    (by norm_num : (0:ℝ)<1) hε hB hBC hr hr1 hs (mul_nonneg hM (Real.sqrt_nonneg K)) hq2
    (initialAtomicRadius_cubic hZpos) hnum hBe heC hR hbar k hG₀ hp₀ hlo G
    (fun j => (hG j).1) HGood hcost
  rw [raw_population_asH1 hd measurableSet_ball] at HF
  have hmono := Coulomb.expectedPopulation_mono (asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1)
    measurableSet_ball measurableSet_ball (Metric.ball_subset_ball (x:=(0:Position)) (show s/4 ≤ (r₀*2^J)/2 by linarith only [hJs']))
  apply hmono.trans (HF.trans ?_)
  have hn : 0 < r₀*2^J := by positivity
  have hflux : A/s^3 ≤ (tfReaction (7*B/128)*(28*Real.pi/3))/(4*Real.pi*(r₀*2^J)^3) := by
    have HH := div_le_div_of_nonneg_left hA.le (pow_pos hn 3) (pow_le_pow_left₀ hn.le hJs 3)
    change A/s^3 ≤ A/(r₀*2^J)^3 at HH
    simpa only [A,div_div,mul_assoc] using HH
  have herr : T*(r₀*2^J)^9 ≤ T*s^9 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn.le hJs 9) hT
  exact add_le_add (sub_le_sub_left hflux _) herr
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_PhysicalOffsetMean
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

theorem zero_offset_physical_core_mean : ∃ t : ℝ,0<t ∧ ∃ Zmin : ℕ,∀ Z : ℕ,Zmin ≤ Z →
    ∀ (hZ : 1 ≤ Z) {N : ℕ} {ψ : Wavefunction (N+1)} {g : Gradient (N+1)},
    ∀ (hd : FormDomain ψ g) (_ : normSquared ψ=1),
    (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)),FormDomain χ h → normSquared χ=1 →
      energy Z ψ g ≤ energy Z χ h) →
    ∀ {E : ℝ},(E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E → (N+1:ℝ) ≤ 3*(Z:ℝ) →
    Coulomb.expectedPopulation (asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1)
      (Metric.ball (0:Position) (2*t)) ≤ (Z:ℝ)-1 := by
  obtain ⟨a,M,ha,hM,H⟩ := physical_propagated_core_mean
  obtain ⟨s₀,hs₀,H⟩ := H 0 (by norm_num)
  have ht : Tendsto (fun s : ℝ => s^3+M*s^12) (𝓝[>] 0) (𝓝 0) := by
    convert ((tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0)).pow 3).add
      (((tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0)).pow 12).const_mul M) using 1 <;> simp
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0,0 < s ∧ s < s₀ ∧ s^3+M*s^12<a :=
    (show ∀ᶠ s : ℝ in 𝓝[>] 0,0 < s from self_mem_nhdsWithin).and (((gt_mem_nhds hs₀).filter_mono nhdsWithin_le_nhds).and (ht.eventually (gt_mem_nhds ha)))
  obtain ⟨s,hs,hss,hsa⟩ := hsmall.exists
  obtain ⟨Zmin,H⟩ := H s hs hss
  refine ⟨s/8,by positivity,Zmin,?_⟩
  intro Z hZm hZ N ψ g hd hn hmin E hE he hnum
  have HH := H Z hZm hZ hd hn hmin hE (by simpa only [add_zero] using he) hnum
  have hnum' : 1+M*s^9 ≤ a/s^3 := by
    apply (le_div_iff₀ (pow_pos hs 3)).mpr
    calc
      _=s^3+M*s^12 := by ring
      _≤a := hsa.le
  have heq : 2*(s/8)=s/4 := by ring
  rw [heq]
  linarith only [HH,hnum']

theorem predecessor_bound_from_attained_physical_state : ∃ D : ℝ,0 ≤ D ∧ ∃ Zmin : ℕ,
    ∀ Z : ℕ,Zmin ≤ Z → ∀ (hZ : 1 ≤ Z) {N : ℕ}
      {ψ : Wavefunction (N+1)} {g : Gradient (N+1)},
    ∀ (_ : FormDomain ψ g) (_ : normSquared ψ=1),
    (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)),FormDomain χ h → normSquared χ=1 →
      energy Z ψ g ≤ energy Z χ h) →
    ∀ {E : ℝ},(E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E → (N+1:ℝ) ≤ 3*(Z:ℝ) →
    (Coulomb.sectorFormBottom (Coulomb.atom Z hZ) (Z-1)).toReal ≤ E+D := by
  obtain ⟨t,ht,Zmin,HM⟩ := zero_offset_physical_core_mean
  obtain ⟨C,hC,HC⟩ := Coulomb.atomic_predecessor_from_physical_mean
  let D := fixedCoreMomentBound t*C*((Coulomb.screenMass 0 (t/4))^2/t+Coulomb.screenMass 0 t/t^2)
  have hD : 0 ≤ D := by
    dsimp [D]
    have hm := (fixedCoreMomentBound_pos t).le
    have hs := (Coulomb.screenMass_pos 0 t).le
    positivity
  refine ⟨D,hD,Zmin,?_⟩
  intro Z hZm hZ N ψ g hd hn hmin E hE he hnum
  let u := asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1
  have hf : Coulomb.form (Coulomb.atom Z hZ) u=energy Z ψ g := asH1_energy Z hZ hd.2.1 hd.2.2.1 hd.2.2.2.1
  exact HC Z hZ u (asH1_antisymmetric hd)
    (by simpa only [u,asH1_mass] using hn) hE (hf.le.trans he) ht
    (HM Z hZm hZ hd hn hmin hE he hnum)
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_LimitTheory_NeutralBaseline
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical
noncomputable section
namespace NeutralAtom

theorem physical_uniform_predecessor_offset : ∃ D:ℝ,0≤D ∧ ∃ Zmin:ℕ,
    ∀ Z:ℕ,Zmin≤Z → ∀ hZ:1≤Z,
    (Coulomb.sectorFormBottom (Coulomb.atom Z hZ) (Z-1)).toReal ≤
      (Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ)).toReal+D := by
  obtain ⟨D,hD,Zmin,H⟩:=predecessor_bound_from_attained_physical_state
  refine ⟨D,hD,Zmin,?_⟩
  intro Z hZm hZ
  obtain ⟨n,hn,hnb,u,ha,hm,he⟩:=Coulomb.atom_global_sector_minimum Z hZ
  obtain ⟨N,hN⟩:=Nat.exists_eq_add_of_le hn
  have hn' : n=N+1 := by omega
  clear hN
  subst n
  have hr:Coulomb.form (Coulomb.atom Z hZ) u=
      (Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ)).toReal := by
    rw [←he,EReal.toReal_coe]
  apply H Z hZm hZ (N:=N) (ψ:=fromH1Wave u) (g:=fromH1Gradient u)
    (fromH1_domain u ha) ((fromH1_mass u).trans hm)
  · intro χ g hd hnorm
    rw [fromH1_energy Z hZ]
    have HH:=Coulomb.unrestrictedFormBottom_le_trial (Coulomb.atom Z hZ)
      (asH1 χ g hd.2.1 hd.2.2.1 hd.2.2.2.1) (asH1_antisymmetric hd)
      ((asH1_mass ..).trans hnorm)
    rw [←he,asH1_energy Z hZ] at HH
    exact EReal.coe_le_coe_iff.mp HH
  · exact (Coulomb.atom_unrestricted_bottom_real Z hZ u ha hm).le
  · rw [fromH1_energy Z hZ,hr]
  · exact_mod_cast hnb

theorem physical_neutral_energy_offset_oai : ∃ D:ℝ,0≤D ∧ ∃ Zmin:ℕ,
    ∀ Z:ℕ,Zmin≤Z → ∀ hZ:1≤Z,
    ∀ {ψ:Wavefunction Z} {g:Gradient Z},FormDomain ψ g → normSquared ψ=1 →
    (∀ (χ:Wavefunction Z) (h:Gradient Z),FormDomain χ h → normSquared χ=1 → energy Z ψ g≤energy Z χ h) →
    energy Z ψ g ≤ (Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ)).toReal+D := by
  obtain ⟨D,hD,Zmin,H⟩:=physical_uniform_predecessor_offset
  refine ⟨D,hD,Zmin,?_⟩
  intro Z hZm hZ ψ g hd hn hmin
  have he:(energy Z ψ g:EReal)=Coulomb.sectorFormBottom (Coulomb.atom Z hZ) Z := by
    rw [←sectorEnergy_eq_formBottom Z hZ]
    apply le_antisymm
    · apply le_sInf
      rintro e ⟨χ,h,hχ,hm,rfl⟩
      exact EReal.coe_le_coe_iff.mpr (hmin χ h hχ hm)
    · exact sectorEnergy_le_trial hd hn
  have hle:Coulomb.sectorFormBottom (Coulomb.atom Z hZ) Z ≤
      Coulomb.sectorFormBottom (Coulomb.atom Z hZ) (Z-1):=
    Coulomb.atom_sectorFormBottom_antitone Z hZ (Nat.sub_le ..)
  have hr:=Coulomb.atom_sectorFormBottom_real Z hZ (Z-1)
  rw [←he,←hr] at hle
  exact (EReal.coe_le_coe_iff.mp hle).trans (H Z hZm hZ)
end NeutralAtom
end

end

end OAI
end

theorem solution : type_of% @OAI.NeutralAtom.physical_neutral_energy_offset_oai := @OAI.NeutralAtom.physical_neutral_energy_offset_oai
