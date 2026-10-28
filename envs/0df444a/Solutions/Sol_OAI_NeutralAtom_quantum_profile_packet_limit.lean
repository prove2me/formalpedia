-- Prove2me | solution 1 for OAI.NeutralAtom.quantum_profile_packet_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:40:44.697616+00:00
-- url     : https://prove2.me/submissions/2f41555c-b355-441f-b883-db1c710a0b00

import Mathlib
import Definitions.Def_CoulombRadii
import Definitions.Def_OAIQ062C008
import Theorems.Thm_OAI_NeutralAtom_physical_neutral_energy_offset

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

theorem integrable_density {N : ℕ} {ψ : Wavefunction (N + 1)}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) : Integrable (density ψ) := by
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro σ _
  exact (integrable_cons (hψ σ).norm.integrable_sq).integral_prod_left

theorem integral_density {N : ℕ} {ψ : Wavefunction (N + 1)}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) :
    (∫ x, density ψ x) = (N + 1 : ℝ) * normSquared ψ := by
  unfold density normSquared
  rw [integral_const_mul, integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro σ _
    exact integral_cons (hψ σ).norm.integrable_sq
  · intro σ _
    exact (integrable_cons (hψ σ).norm.integrable_sq).integral_prod_left

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

theorem expectation_error_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hY : MemLp Y 2 μ) (hY0 : 0 ≤ᵐ[μ] Y)
    {G : Set Ω} (hG : MeasurableSet G) {δ C L : ℝ}
    (hδ : 0 ≤ δ) (hgood : ∀ z ∈ G, |Y z - L| ≤ δ)
    (hL2 : Real.sqrt (∫ z, Y z ^ 2 ∂μ) ≤ C) :
    |(∫ z, Y z ∂μ) - L| ≤ δ + C * Real.sqrt (μ.real Gᶜ) + |L| * μ.real Gᶜ := by
  have hi : Integrable Y μ := hY.integrable (by norm_num)
  have heq : (∫ z, Y z ∂μ) - L =
      (∫ z in G, Y z - L ∂μ) + ((∫ z in Gᶜ, Y z ∂μ) - μ.real Gᶜ * L) := by
    have hsplit := integral_add_compl hG (hi.sub (integrable_const L))
    simp only [Pi.sub_apply] at hsplit
    rw [integral_sub hi (integrable_const L), integral_const] at hsplit
    rw [integral_sub (μ := μ.restrict Gᶜ) hi.integrableOn (integrable_const L),
      setIntegral_const] at hsplit
    simpa [smul_eq_mul] using hsplit.symm
  have hA : |∫ z in G, Y z - L ∂μ| ≤ δ := by
    have h := norm_setIntegral_le_of_norm_le_const (f := fun z => Y z - L) (C := δ)
      (measure_lt_top μ G)
      (fun z hz => by simpa only [Real.norm_eq_abs] using hgood z hz)
    calc
      _ ≤ δ * μ.real G := by simpa only [Real.norm_eq_abs] using h
      _ ≤ δ := by nlinarith [measureReal_le_one (μ := μ) (s := G)]
  have hB0 : 0 ≤ ∫ z in Gᶜ, Y z ∂μ := integral_nonneg_of_ae (ae_restrict_of_ae hY0)
  have hB : (∫ z in Gᶜ, Y z ∂μ) ≤ C * Real.sqrt (μ.real Gᶜ) :=
    (exceptional_event_bound hY hY0 hG.compl).trans
      (mul_le_mul_of_nonneg_right hL2 (Real.sqrt_nonneg _))
  rw [heq]
  calc
    _ ≤ |∫ z in G, Y z - L ∂μ| +
        |(∫ z in Gᶜ, Y z ∂μ) - μ.real Gᶜ * L| := abs_add_le _ _
    _ ≤ |∫ z in G, Y z - L ∂μ| +
        (|∫ z in Gᶜ, Y z ∂μ| + |μ.real Gᶜ * L|) :=
      add_le_add le_rfl (abs_sub _ _)
    _ = |∫ z in G, Y z - L ∂μ| +
        ((∫ z in Gᶜ, Y z ∂μ) + μ.real Gᶜ * |L|) := by
      rw [abs_of_nonneg hB0, abs_mul, abs_of_nonneg measureReal_nonneg]
    _ ≤ _ := by linarith

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

theorem packetKernel_clamped_support (g : Position → ℝ)
    (hg : ∀ x, 1 < ‖x‖ → g x = 0) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (z y : Position)
    (hz : ‖z‖ ≤ r₀) (hK : packetKernel g c₁ r₀ s z y ≠ 0) :
    ‖y‖ ≤ (1+c₁*s^packetExponent)*r₀ := by
  have hd := (packetKernel_support g hg hc hr hs z y hK).trans
    (packetWidth_le c₁ r₀ s hc.le hr hs z)
  rw [max_eq_right hz] at hd
  have hn := norm_sub_norm_le y z
  nlinarith

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
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_WeakLaplacian
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

theorem WeakLaplacianLower.mono {f : Position → ℝ} {U V : Set Position} {c : ℝ}
    (h : WeakLaplacianLower f U c) (he : V ⊆ U) : WeakLaplacianLower f V c := by
  intro φ hφ hc ht hp
  exact h φ hφ hc (ht.trans he) hp

theorem coordinateLaplacian_neg (f : Position → ℝ) (x : Position) :
    coordinateLaplacian (fun y => -f y) x = -coordinateLaplacian f x := by
  unfold coordinateLaplacian
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have he : deriv (fun t : ℝ => -f (x+t • axis a)) =
      -deriv (fun t : ℝ => f (x+t • axis a)) := by ext t; exact deriv.neg
  rw [he, deriv.neg]

theorem HasWeakLaplacian.neg {f q : Position → ℝ} {U : Set Position}
    (h : HasWeakLaplacian f U q) :
    HasWeakLaplacian (fun x => -f x) U (fun x => -q x) := by
  intro φ hφ hc ht
  simpa only [neg_mul, integral_neg] using congrArg Neg.neg (h φ hφ hc ht)

theorem weakLaplacian_ge_at_local_min {f q b : Position → ℝ} {U : Set Position}
    {o : Position} (ho : IsOpen U) (hx : o ∈ U)
    (hf : ContinuousOn f U) (hq : ContinuousOn q U) (hb : ContDiffOn ℝ 2 b U)
    (hw : HasWeakLaplacian f U q) (hm : IsLocalMin (fun x => f x-b x) o) :
    coordinateLaplacian b o ≤ q o := by
  have hm' : IsLocalMax (fun x => (-f x)-(-b x)) o := by
    filter_upwards [hm] with x hx
    linarith
  have h := weakLaplacian_le_at_local_max ho hx hf.neg hq.neg hb.neg hw.neg hm'
  rw [coordinateLaplacian_neg] at h
  exact neg_le_neg_iff.mp h

theorem contDiffOn_radialBarrier (a d : ℝ) (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (radialBarrier a d) punctured :=
  (contDiffOn_const.mul (contDiffOn_radialPower (-2) n)).add
    (contDiffOn_const.mul ((contDiffOn_radialPower (-1) n).add (contDiffOn_radialPower (-3) n)))

theorem radialBarrier_scaled {x : Position} (hx : x ≠ 0) (a d : ℝ) :
    (‖x‖^2)^2 * radialBarrier a d x = a+d*((‖x‖^2)+(‖x‖^2)⁻¹) := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  norm_num [radialBarrier, radialPower, Real.rpow_neg_natCast, Real.rpow_neg_one]
  field_simp

theorem laplacian_radialBarrier_scaled {x : Position} (hx : x ≠ 0) (a d : ℝ) :
    (‖x‖^2)^3 * coordinateLaplacian (radialBarrier a d) x =
      12*a+d*(2*(‖x‖^2)+30*(‖x‖^2)⁻¹) := by
  have hcp (p : ℝ) : ContDiffAt ℝ 2 (radialPower p) x :=
    (contDiffOn_radialPower p 2).contDiffAt (isOpen_punctured.mem_nhds hx)
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  unfold radialBarrier
  rw [coordinateLaplacian_add_at (contDiffAt_const.mul (hcp (-2)))
      (contDiffAt_const.mul ((hcp (-1)).add (hcp (-3)))),
    coordinateLaplacian_const_mul, coordinateLaplacian_const_mul,
    coordinateLaplacian_add_at (hcp (-1)) (hcp (-3))]
  simp only [coordinateLaplacian_radialPower hx]
  norm_num [Real.rpow_neg_natCast, Real.rpow_neg_one]
  field_simp

theorem radialPenalty_pos {x : Position} (hx : x ≠ 0) : 0 < radialPenalty x := by
  unfold radialPenalty
  exact add_pos (sq_pos_of_pos (norm_pos_iff.mpr hx)) (inv_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr hx)))

theorem continuousOn_radialPenalty : ContinuousOn radialPenalty punctured :=
  (continuous_norm.pow 2).continuousOn.add
    ((continuous_norm.pow 2).continuousOn.inv₀ (fun _ hx => pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)))

theorem exists_penalized_max {V : Position → ℝ} {C δ : ℝ} {x₀ : Position}
    (hV : ContinuousOn V punctured) (hC : ∀ x ≠ 0, V x ≤ C) (hδ : 0 < δ)
    (hx₀ : x₀ ≠ 0) :
    ∃ x, x ≠ 0 ∧ ∀ y ≠ 0, V y-δ*radialPenalty y ≤ V x-δ*radialPenalty x := by
  let T := C-(V x₀-δ*radialPenalty x₀)+1
  have hT : 0 < T := by
    dsimp [T]
    nlinarith [hC x₀ hx₀, mul_pos hδ (radialPenalty_pos hx₀)]
  let α := min (‖x₀‖^2) (δ/T)/2
  let β := max (‖x₀‖^2) (T/δ)+1
  have hq₀ : 0 < ‖x₀‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hx₀)
  have hα : 0 < α := by dsimp [α]; positivity
  have hβ : 0 < β := by dsimp [β]; positivity
  have hαq : α ≤ ‖x₀‖^2 := by
    dsimp [α]
    have := min_le_left (‖x₀‖^2) (δ/T)
    linarith
  have hαT : α ≤ δ/T := by
    dsimp [α]
    have := min_le_right (‖x₀‖^2) (δ/T)
    have := div_pos hδ hT
    linarith
  have hqβ : ‖x₀‖^2 ≤ β := by
    dsimp [β]
    have := le_max_left (‖x₀‖^2) (T/δ)
    linarith
  have hTβ : T/δ ≤ β := by
    dsimp [β]
    have := le_max_right (‖x₀‖^2) (T/δ)
    linarith
  let K : Set Position := {x | α ≤ ‖x‖^2 ∧ ‖x‖^2 ≤ β}
  have hKclosed : IsClosed K := isClosed_Icc.preimage (continuous_norm.pow 2)
  have hKsub : K ⊆ Metric.closedBall 0 (β+1) := by
    intro x hx
    simp only [Metric.mem_closedBall, dist_zero_right]
    have hu := hx.2
    nlinarith [sq_nonneg (‖x‖-1)]
  have hK : IsCompact K := (isCompact_closedBall (0 : Position) (β+1)).of_isClosed_subset hKclosed hKsub
  have hKp : K ⊆ punctured := by
    intro x hx hn
    subst x
    simpa using lt_of_lt_of_le hα hx.1
  have hcont : ContinuousOn (fun x => V x-δ*radialPenalty x) K :=
    (hV.sub (continuousOn_const.mul continuousOn_radialPenalty)).mono hKp
  obtain ⟨x, hx, hxm⟩ := hK.exists_isMaxOn ⟨x₀, hαq, hqβ⟩ hcont
  refine ⟨x, hKp hx, ?_⟩
  intro y hy
  by_cases hyK : y ∈ K
  · exact hxm hyK
  have hqy : 0 < ‖y‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hy)
  have hYP : T < δ*radialPenalty y := by
    by_cases hyl : α ≤ ‖y‖^2
    · have hyh : β < ‖y‖^2 := lt_of_not_ge (fun hn => hyK ⟨hyl, hn⟩)
      have htq : T < (‖y‖^2)*δ := (div_lt_iff₀ hδ).mp (lt_of_le_of_lt hTβ hyh)
      dsimp [radialPenalty]
      nlinarith [mul_nonneg hδ.le (inv_nonneg.mpr hqy.le)]
    · have hylo : ‖y‖^2 < δ/T := lt_of_lt_of_le (lt_of_not_ge hyl) hαT
      have htq : (‖y‖^2)*T < δ := (lt_div_iff₀ hT).mp hylo
      have htid : T < δ/(‖y‖^2) := (lt_div_iff₀ hqy).mpr (by nlinarith)
      dsimp [radialPenalty]
      rw [div_eq_mul_inv] at htid
      nlinarith [mul_pos hδ hqy]
  have hxm₀ : V x₀-δ*radialPenalty x₀ ≤ V x-δ*radialPenalty x := hxm ⟨hαq, hqβ⟩
  dsimp [T] at hYP
  linarith [hC y hy]

theorem exists_penalized_min {V : Position → ℝ} {B δ : ℝ} {x₀ : Position}
    (hV : ContinuousOn V punctured) (hB : ∀ x ≠ 0, B ≤ V x) (hδ : 0 < δ)
    (hx₀ : x₀ ≠ 0) :
    ∃ x, x ≠ 0 ∧ ∀ y ≠ 0, V x+δ*radialPenalty x ≤ V y+δ*radialPenalty y := by
  obtain ⟨x, hx, hxm⟩ := exists_penalized_max hV.neg (C := -B)
    (fun y hy => neg_le_neg (hB y hy)) hδ hx₀
  refine ⟨x, hx, ?_⟩
  intro y hy
  have hh := hxm y hy
  simp only [Pi.neg_apply] at hh
  linarith

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_CoulombKernel
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

theorem radial_integral_exterior (f : ℝ → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    (∫ x : Position in {x | a < ‖x‖}, f ‖x‖) =
      (4*Real.pi) * ∫ r : ℝ in Set.Ioi a, r^2*f r := by
  have hS : MeasurableSet {x : Position | a < ‖x‖} :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  rw [← integral_indicator hS]
  have hid : (fun x : Position => Set.indicator {x : Position | a < ‖x‖} (fun x => f ‖x‖) x) =
      (fun x : Position => (Set.Ioi a).indicator f ‖x‖) := by
    ext x
    by_cases hx : a < ‖x‖ <;> simp [hx]
  rw [hid, integral_fun_norm_addHaar volume]
  have hinner : (∫ r in Set.Ioi (0:ℝ), r^(Module.finrank ℝ Position-1) • (Set.Ioi a).indicator f r) =
      ∫ r in Set.Ioi a, r^2*f r := by
    simp only [finrank_euclideanSpace_fin]
    norm_num
    have heq : (fun r : ℝ => r^2*(Set.Ioi a).indicator f r) =
        (Set.Ioi a).indicator (fun r => r^2*f r) := by
      ext r
      by_cases hr : r ∈ Set.Ioi a <;> simp [hr]
    rw [heq, setIntegral_indicator measurableSet_Ioi]
    rw [Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi ha)]
  rw [hinner]
  simp only [Measure.real, EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one, one_pow,
    one_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi*4/3), smul_eq_mul,
    nsmul_eq_mul]
  norm_num [Position, finrank_euclideanSpace_fin]
  ring

theorem radial_integrable_exterior (f : ℝ → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun x : Position => f ‖x‖) {x | a < ‖x‖} ↔
      IntegrableOn (fun r : ℝ => r^2*f r) (Set.Ioi a) := by
  have hS : MeasurableSet {x : Position | a < ‖x‖} :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  rw [← integrable_indicator_iff hS]
  change Integrable (fun x : Position => Set.indicator {x : Position | a < ‖x‖} (fun x => f ‖x‖) x) ↔ _
  have hid : (fun x : Position => Set.indicator {x : Position | a < ‖x‖} (fun x => f ‖x‖) x) =
      (fun x : Position => (Set.Ioi a).indicator f ‖x‖) := by
    ext x
    by_cases hx : a < ‖x‖ <;> simp [hx]
  rw [hid, integrable_fun_norm_addHaar volume]
  simp only [finrank_euclideanSpace_fin]
  norm_num
  have heq : (fun r : ℝ => r^2*(Set.Ioi a).indicator f r) =
      (Set.Ioi a).indicator (fun r => r^2*f r) := by
    ext r
    by_cases hr : r ∈ Set.Ioi a <;> simp [hr]
  rw [heq, integrableOn_indicator_iff measurableSet_Ioi,
    Set.inter_eq_left.mpr (Set.Ioi_subset_Ioi ha)]

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_ScaledProfile
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

theorem continuousOn_scaledProfile {F : Position → ℝ} (hF : ContinuousOn F punctured) :
    ContinuousOn (scaledProfile F) punctured :=
  ((continuous_norm.pow 2).pow 2).continuousOn.mul hF

theorem scaled_reaction {F : Position → ℝ} {x : Position} (hF : 0 ≤ F x) (c : ℝ) :
    (‖x‖^2)^3*(c*F x^(3/2 : ℝ)) = c*(scaledProfile F x)^(3/2 : ℝ) := by
  have hp : ((‖x‖^2)^2)^(3/2 : ℝ) = (‖x‖^2)^3 := by
    rw [← Real.rpow_natCast (‖x‖^2) 2, ← Real.rpow_mul (sq_nonneg ‖x‖)]
    norm_num
  rw [scaledProfile, Real.mul_rpow (sq_nonneg _) hF, hp]
  ring

theorem penalized_max_reaction_bound {F : Position → ℝ} {c δ : ℝ} {x : Position}
    (hF : ContinuousOn F punctured) (hpos : ∀ y ≠ 0, 0 ≤ F y)
    (hw : HasWeakLaplacian F punctured (fun y => c*F y^(3/2 : ℝ)))
    (hδ : 0 < δ) (hx : x ≠ 0)
    (hm : ∀ y ≠ 0, scaledProfile F y-δ*radialPenalty y ≤ scaledProfile F x-δ*radialPenalty x) :
    c*(scaledProfile F x)^(3/2 : ℝ) ≤ 12*scaledProfile F x+18*(δ*radialPenalty x) := by
  let a := scaledProfile F x-δ*radialPenalty x
  have hbar (y : Position) (hy : y ≠ 0) : F y ≤ radialBarrier a δ y := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos (sq_pos_of_pos (norm_pos_iff.mpr hy)))).mp
    change scaledProfile F y ≤ (‖y‖^2)^2*radialBarrier a δ y
    rw [radialBarrier_scaled hy]
    have hh := hm y hy
    dsimp [a, radialPenalty] at *
    linarith
  have he : F x = radialBarrier a δ x := by
    apply (mul_left_cancel₀ (pow_ne_zero 2 (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))))
    change scaledProfile F x = (‖x‖^2)^2*radialBarrier a δ x
    rw [radialBarrier_scaled hx]
    simp [a, radialPenalty]
  have hlmax : IsLocalMax (fun y => F y-radialBarrier a δ y) x := by
    filter_upwards [isOpen_punctured.mem_nhds hx] with y hy
    rw [he, sub_self]
    exact sub_nonpos.mpr (hbar y hy)
  have hq : ContinuousOn (fun y => c*F y^(3/2 : ℝ)) punctured :=
    continuousOn_const.mul (hF.rpow_const (fun _ _ => Or.inr (by norm_num)))
  have h := weakLaplacian_le_at_local_max isOpen_punctured hx hF hq
    (contDiffOn_radialBarrier a δ 2) hw hlmax
  have hmul := mul_le_mul_of_nonneg_left h (pow_nonneg (sq_nonneg ‖x‖) 3)
  rw [scaled_reaction (hpos x hx), laplacian_radialBarrier_scaled hx] at hmul
  have hδq : 0 ≤ δ*(‖x‖^2) := mul_nonneg hδ.le (sq_nonneg ‖x‖)
  dsimp [a, radialPenalty] at *
  nlinarith

theorem penalized_min_reaction_bound {F : Position → ℝ} {c δ : ℝ} {x : Position}
    (hF : ContinuousOn F punctured) (hpos : ∀ y ≠ 0, 0 ≤ F y)
    (hw : HasWeakLaplacian F punctured (fun y => c*F y^(3/2 : ℝ)))
    (hδ : 0 < δ) (hx : x ≠ 0)
    (hm : ∀ y ≠ 0, scaledProfile F x+δ*radialPenalty x ≤ scaledProfile F y+δ*radialPenalty y) :
    12*scaledProfile F x-18*(δ*radialPenalty x) ≤ c*(scaledProfile F x)^(3/2 : ℝ) := by
  let a := scaledProfile F x+δ*radialPenalty x
  have hbar (y : Position) (hy : y ≠ 0) : radialBarrier a (-δ) y ≤ F y := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos (sq_pos_of_pos (norm_pos_iff.mpr hy)))).mp
    change (‖y‖^2)^2*radialBarrier a (-δ) y ≤ scaledProfile F y
    rw [radialBarrier_scaled hy]
    have hh := hm y hy
    dsimp [a, radialPenalty] at *
    linarith
  have he : F x = radialBarrier a (-δ) x := by
    apply (mul_left_cancel₀ (pow_ne_zero 2 (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))))
    change scaledProfile F x = (‖x‖^2)^2*radialBarrier a (-δ) x
    rw [radialBarrier_scaled hx]
    simp [a, radialPenalty]
  have hlmin : IsLocalMin (fun y => F y-radialBarrier a (-δ) y) x := by
    filter_upwards [isOpen_punctured.mem_nhds hx] with y hy
    rw [he, sub_self]
    exact sub_nonneg.mpr (hbar y hy)
  have hq : ContinuousOn (fun y => c*F y^(3/2 : ℝ)) punctured :=
    continuousOn_const.mul (hF.rpow_const (fun _ _ => Or.inr (by norm_num)))
  have h := weakLaplacian_ge_at_local_min isOpen_punctured hx hF hq
    (contDiffOn_radialBarrier a (-δ) 2) hw hlmin
  have hmul := mul_le_mul_of_nonneg_left h (pow_nonneg (sq_nonneg ‖x‖) 3)
  rw [scaled_reaction (hpos x hx), laplacian_radialBarrier_scaled hx] at hmul
  have hδq : 0 ≤ δ*(‖x‖^2) := mul_nonneg hδ.le (sq_nonneg ‖x‖)
  dsimp [a, radialPenalty] at *
  nlinarith

theorem exists_approximate_penalized_max {V : Position → ℝ} {b ε : ℝ}
    (hV : ContinuousOn V punctured) (hb : ∀ x ≠ 0, V x ≤ b)
    (hnear : ∀ e > 0, ∃ x ≠ 0, b-e < V x) (hε : 0 < ε) :
    ∃ δ > 0, ∃ x ≠ 0,
      (∀ y ≠ 0, V y-δ*radialPenalty y ≤ V x-δ*radialPenalty x) ∧
      b-ε < V x ∧ δ*radialPenalty x < ε := by
  obtain ⟨x₀, hx₀, hx₀v⟩ := hnear (ε/2) (by positivity)
  let δ := (ε/2)/radialPenalty x₀
  have hδ : 0 < δ := div_pos (by positivity) (radialPenalty_pos hx₀)
  have hδ₀ : δ*radialPenalty x₀ = ε/2 := div_mul_cancel₀ _ (radialPenalty_pos hx₀).ne'
  obtain ⟨x, hx, hxm⟩ := exists_penalized_max hV hb hδ hx₀
  have hh := hxm x₀ hx₀
  rw [hδ₀] at hh
  have hM : b-ε < V x-δ*radialPenalty x := by linarith
  refine ⟨δ, hδ, x, hx, hxm, ?_, ?_⟩
  · have hp := mul_pos hδ (radialPenalty_pos hx)
    linarith
  · linarith [hb x hx]

theorem exists_approximate_penalized_min {V : Position → ℝ} {b ε : ℝ}
    (hV : ContinuousOn V punctured) (hb : ∀ x ≠ 0, b ≤ V x)
    (hnear : ∀ e > 0, ∃ x ≠ 0, V x < b+e) (hε : 0 < ε) :
    ∃ δ > 0, ∃ x ≠ 0,
      (∀ y ≠ 0, V x+δ*radialPenalty x ≤ V y+δ*radialPenalty y) ∧
      V x < b+ε ∧ δ*radialPenalty x < ε := by
  obtain ⟨x₀, hx₀, hx₀v⟩ := hnear (ε/2) (by positivity)
  let δ := (ε/2)/radialPenalty x₀
  have hδ : 0 < δ := div_pos (by positivity) (radialPenalty_pos hx₀)
  have hδ₀ : δ*radialPenalty x₀ = ε/2 := div_mul_cancel₀ _ (radialPenalty_pos hx₀).ne'
  obtain ⟨x, hx, hxm⟩ := exists_penalized_min hV hb hδ hx₀
  have hh := hxm x₀ hx₀
  rw [hδ₀] at hh
  have hM : V x+δ*radialPenalty x < b+ε := by linarith
  refine ⟨δ, hδ, x, hx, hxm, ?_, ?_⟩
  · have hp := mul_pos hδ (radialPenalty_pos hx)
    linarith
  · linarith [hb x hx]

theorem reaction_le_at_supremum {F : Position → ℝ} {c b : ℝ}
    (hF : ContinuousOn F punctured) (hpos : ∀ y ≠ 0, 0 ≤ F y)
    (hw : HasWeakLaplacian F punctured (fun y => c*F y^(3/2 : ℝ)))
    (hb : ∀ x ≠ 0, scaledProfile F x ≤ b)
    (hnear : ∀ e > 0, ∃ x ≠ 0, b-e < scaledProfile F x) :
    c*b^(3/2 : ℝ) ≤ 12*b := by
  have happ (ε : ℝ) (hε : 0 < ε) :
      ∃ t : ℝ, b-ε < t ∧ t ≤ b ∧ c*t^(3/2 : ℝ) ≤ 12*t+18*ε := by
    obtain ⟨δ, hδ, x, hx, hxm, hxb, hδx⟩ :=
      exists_approximate_penalized_max (continuousOn_scaledProfile hF) hb hnear hε
    refine ⟨scaledProfile F x, hxb, hb x hx, ?_⟩
    linarith [penalized_max_reaction_bound hF hpos hw hδ hx hxm]
  let e : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have he : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose t htl htu htr using fun n => happ (e n) (by dsimp [e]; positivity)
  have ht : Tendsto t atTop (𝓝 b) :=
    (show Tendsto (fun n => b-e n) atTop (𝓝 b) by simpa using tendsto_const_nhds.sub he).squeeze
      tendsto_const_nhds (fun n => (htl n).le) htu
  have hr : Tendsto (fun n => c*(t n)^(3/2 : ℝ)) atTop (𝓝 (c*b^(3/2 : ℝ))) :=
    tendsto_const_nhds.mul (ht.rpow_const (Or.inr (by norm_num)))
  have hs : Tendsto (fun n => 12*t n+18*e n) atTop (𝓝 (12*b)) := by
    simpa using (tendsto_const_nhds.mul ht).add (tendsto_const_nhds.mul he)
  exact le_of_tendsto_of_tendsto' hr hs htr

theorem reaction_ge_at_infimum {F : Position → ℝ} {c b : ℝ}
    (hF : ContinuousOn F punctured) (hpos : ∀ y ≠ 0, 0 ≤ F y)
    (hw : HasWeakLaplacian F punctured (fun y => c*F y^(3/2 : ℝ)))
    (hb : ∀ x ≠ 0, b ≤ scaledProfile F x)
    (hnear : ∀ e > 0, ∃ x ≠ 0, scaledProfile F x < b+e) :
    12*b ≤ c*b^(3/2 : ℝ) := by
  have happ (ε : ℝ) (hε : 0 < ε) :
      ∃ t : ℝ, b ≤ t ∧ t < b+ε ∧ 12*t-18*ε ≤ c*t^(3/2 : ℝ) := by
    obtain ⟨δ, hδ, x, hx, hxm, hxb, hδx⟩ :=
      exists_approximate_penalized_min (continuousOn_scaledProfile hF) hb hnear hε
    refine ⟨scaledProfile F x, hb x hx, hxb, ?_⟩
    linarith [penalized_min_reaction_bound hF hpos hw hδ hx hxm]
  let e : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have he : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose t htl htu htr using fun n => happ (e n) (by dsimp [e]; positivity)
  have ht : Tendsto t atTop (𝓝 b) := tendsto_const_nhds.squeeze
    (show Tendsto (fun n => b+e n) atTop (𝓝 b) by simpa using tendsto_const_nhds.add he)
      htl (fun n => (htu n).le)
  have hr : Tendsto (fun n => c*(t n)^(3/2 : ℝ)) atTop (𝓝 (c*b^(3/2 : ℝ))) :=
    tendsto_const_nhds.mul (ht.rpow_const (Or.inr (by norm_num)))
  have hs : Tendsto (fun n => 12*t n-18*e n) atTop (𝓝 (12*b)) := by
    simpa using (tendsto_const_nhds.mul ht).sub (tendsto_const_nhds.mul he)
  exact le_of_tendsto_of_tendsto' hs hr htr

theorem scalar_upper_contact {c b : ℝ} (hc : 0 < c) (hb : 0 < b)
    (h : c*b^(3/2 : ℝ) ≤ 12*b) : b ≤ (12/c)^2 := by
  have hr : b^(3/2 : ℝ) = b*Real.sqrt b := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hb.le (by norm_num : (1:ℝ)+1/2 ≠ 0)]
    norm_num
  rw [hr] at h
  have hs : c*Real.sqrt b ≤ 12 := by nlinarith
  have hs' : Real.sqrt b ≤ 12/c := (le_div_iff₀ hc).mpr (by nlinarith)
  nlinarith [sq_nonneg (12/c-Real.sqrt b), Real.sq_sqrt hb.le, Real.sqrt_nonneg b]

theorem scalar_lower_contact {c b : ℝ} (hc : 0 < c) (hb : 0 < b)
    (h : 12*b ≤ c*b^(3/2 : ℝ)) : (12/c)^2 ≤ b := by
  have hr : b^(3/2 : ℝ) = b*Real.sqrt b := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hb.le (by norm_num : (1:ℝ)+1/2 ≠ 0)]
    norm_num
  rw [hr] at h
  have hs : 12 ≤ c*Real.sqrt b := by nlinarith
  have hs' : 12/c ≤ Real.sqrt b := (div_le_iff₀ hc).mpr (by nlinarith)
  have hp : 0 < 12/c := by positivity
  nlinarith [Real.sq_sqrt hb.le, Real.sqrt_nonneg b]

theorem weak_sommerfeld_rigidity {F : Position → ℝ} {c B C : ℝ}
    (hc : 0 < c) (hB : 0 < B)
    (hF : ContinuousOn F punctured)
    (hw : HasWeakLaplacian F punctured (fun x => c*F x^(3/2 : ℝ)))
    (hbounds : ∀ x ≠ 0, B ≤ scaledProfile F x ∧ scaledProfile F x ≤ C) :
    ∀ x ≠ 0, F x = (12/c)^2*radialPower (-2) x := by
  let S : Set ℝ := scaledProfile F '' punctured
  have hx₀ : axis 0 ≠ 0 := by
    intro h
    have h' := congrArg (fun x : Position => x 0) h
    norm_num [axis] at h'
  have hS : S.Nonempty := ⟨scaledProfile F (axis 0), ⟨axis 0, hx₀, rfl⟩⟩
  have hSu : BddAbove S := ⟨C, by rintro _ ⟨x, hx, rfl⟩; exact (hbounds x hx).2⟩
  have hSl : BddBelow S := ⟨B, by rintro _ ⟨x, hx, rfl⟩; exact (hbounds x hx).1⟩
  have hmax (x : Position) (hx : x ≠ 0) : scaledProfile F x ≤ sSup S :=
    le_csSup hSu ⟨x, hx, rfl⟩
  have hmin (x : Position) (hx : x ≠ 0) : sInf S ≤ scaledProfile F x :=
    csInf_le hSl ⟨x, hx, rfl⟩
  have hpos (x : Position) (hx : x ≠ 0) : 0 ≤ F x := by
    have hp : 0 ≤ scaledProfile F x := le_trans hB.le (hbounds x hx).1
    exact nonneg_of_mul_nonneg_right hp (sq_pos_of_pos (sq_pos_of_pos (norm_pos_iff.mpr hx)))
  have hnearU (e : ℝ) (he : 0 < e) : ∃ x ≠ 0, sSup S-e < scaledProfile F x := by
    obtain ⟨v, ⟨x, hx, rfl⟩, hv⟩ := exists_lt_of_lt_csSup hS (sub_lt_self _ he)
    exact ⟨x, hx, hv⟩
  have hnearL (e : ℝ) (he : 0 < e) : ∃ x ≠ 0, scaledProfile F x < sInf S+e := by
    obtain ⟨v, ⟨x, hx, rfl⟩, hv⟩ := exists_lt_of_csInf_lt hS (lt_add_of_pos_right _ he)
    exact ⟨x, hx, hv⟩
  have hBp : 0 < sInf S := lt_of_lt_of_le hB (le_csInf hS (by
    rintro _ ⟨x, hx, rfl⟩; exact (hbounds x hx).1))
  have hCp : 0 < sSup S := lt_of_lt_of_le
    (lt_of_lt_of_le hB (hbounds (axis 0) hx₀).1) (hmax (axis 0) hx₀)
  have hupper := scalar_upper_contact hc hCp (reaction_le_at_supremum hF hpos hw hmax hnearU)
  have hlower := scalar_lower_contact hc hBp (reaction_ge_at_infimum hF hpos hw hmin hnearL)
  intro x hx
  have he : scaledProfile F x = (12/c)^2 := le_antisymm
    (le_trans (hmax x hx) hupper) (le_trans hlower (hmin x hx))
  have hq : ‖x‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  unfold scaledProfile at he
  have he' : F x = (12/c)^2 / (‖x‖^2)^2 :=
    (eq_div_iff (pow_ne_zero 2 hq)).mpr (by nlinarith [he])
  rw [he']
  norm_num [radialPower, Real.rpow_neg_natCast, div_eq_mul_inv]

theorem WeakLaplacianLower.add_smooth {f b : Position → ℝ}
    {U : Set Position} {c d : ℝ}
    (hf : ∀ x ∈ U, ContinuousAt f x) (hb : ∀ x ∈ U, ContDiffAt ℝ 2 b x)
    (hw : WeakLaplacianLower f U c)
    (hl : ∀ x ∈ U, d ≤ coordinateLaplacian b x) :
    WeakLaplacianLower (fun x => f x+b x) U (c+d) := by
  intro φ hφ hc ht hp
  have hts : tsupport (coordinateLaplacian φ) ⊆ tsupport φ := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro x hx
    by_contra hn
    exact hx (coordinateLaplacian_eq_zero_of_notMem_tsupport hn)
  have hφ2 := hφ.of_le (show (2 : WithTop ℕ∞) ≤ ∞ by exact WithTop.coe_le_coe.mpr le_top)
  have hφl := continuous_coordinateLaplacian hφ2
  have hφlc := hasCompactSupport_coordinateLaplacian hc
  have hif : Integrable (fun x => f x*coordinateLaplacian φ x) :=
    integrable_mul_compact_of_continuousAt (fun x hx => hf x (ht (hts hx))) hφl hφlc
  have hib : Integrable (fun x => b x*coordinateLaplacian φ x) :=
    integrable_mul_compact_of_continuousAt (fun x hx => (hb x (ht (hts hx))).continuousAt) hφl hφlc
  have hib' : Integrable (fun x => coordinateLaplacian b x*φ x) :=
    integrable_mul_compact_of_continuousAt
      (fun x hx => continuousAt_coordinateLaplacian (hb x (ht hx))) hφ.continuous hc
  have hbd : d*(∫ x, φ x) ≤ ∫ x, coordinateLaplacian b x*φ x := by
    rw [← integral_const_mul]
    apply integral_mono ((hφ.continuous.integrable_of_hasCompactSupport hc).const_mul d) hib'
    intro x
    by_cases hx : x ∈ tsupport φ
    · exact mul_le_mul_of_nonneg_right (hl x (ht hx)) (hp x)
    · simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero, le_refl]
  simp_rw [add_mul]
  rw [integral_add hif hib, integral_mul_coordinateLaplacian_eq (fun x hx => hb x (ht hx)) hφ hc]
  linarith [hw φ hφ hc ht hp]

theorem weak_maximum_principle_closedBall {f : Position → ℝ} {R : ℝ}
    (hR : 0 < R) (hf : ContinuousOn f (Metric.closedBall 0 R))
    (hbdy : ∀ x : Position, ‖x‖ = R → f x ≤ 0)
    (hw : WeakLaplacianLower f (Metric.ball 0 R ∩ {x | 0 < f x}) 0) :
    ∀ x ∈ Metric.closedBall 0 R, f x ≤ 0 := by
  intro x₀ hx₀
  by_contra hn
  have hp : 0 < f x₀ := lt_of_not_ge hn
  let η := f x₀/(2*R^2)
  have hη : 0 < η := by dsimp [η]; positivity
  have hηR : η*R^2 = f x₀/2 := by dsimp [η]; field_simp
  let v : Position → ℝ := fun x => f x+η*‖x‖^2
  have hq : ContDiff ℝ 2 (fun x : Position => η*‖x‖^2) := contDiff_const.mul (contDiff_norm_sq ℝ)
  have hv : ContinuousOn v (Metric.closedBall 0 R) := hf.add hq.continuous.continuousOn
  obtain ⟨x, hx, hxm⟩ := (isCompact_closedBall (0 : Position) R).exists_isMaxOn
    ⟨x₀, hx₀⟩ hv
  have hhigh : η*R^2 < v x := by
    have hh := hxm hx₀
    have hq₀ := mul_nonneg hη.le (sq_nonneg ‖x₀‖)
    dsimp [v] at *
    linarith
  have hxnorm : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hxint : x ∈ Metric.ball 0 R := by
    simp only [Metric.mem_ball, dist_zero_right]
    by_contra hn
    have he : ‖x‖ = R := le_antisymm hxnorm (le_of_not_gt hn)
    have hh := hbdy x he
    dsimp [v] at hhigh
    rw [he] at hhigh
    linarith
  have hfx : 0 < f x := by
    have hqle : η*‖x‖^2 ≤ η*R^2 := mul_le_mul_of_nonneg_left
      (sq_le_sq₀ (norm_nonneg _) hR.le |>.mpr hxnorm) hη.le
    dsimp [v] at hhigh
    linarith
  let U := Metric.ball (0 : Position) R ∩ {x | 0 < f x}
  have hcont : ContinuousAt f x := hf.continuousAt
    (mem_of_superset (Metric.isOpen_ball.mem_nhds hxint) Metric.ball_subset_closedBall)
  have hun : U ∈ 𝓝 x := inter_mem (Metric.isOpen_ball.mem_nhds hxint)
    (hcont.eventually (Ioi_mem_nhds hfx))
  obtain ⟨r, hr, hsub⟩ : ∃ r > 0, Metric.closedBall x r ⊆ U :=
    Metric.nhds_basis_closedBall.mem_iff.mp hun
  have hlocal : WeakLaplacianLower v (Metric.ball x r) (6*η) := by
    have hadd := hw.add_smooth
      (fun y hy => hf.continuousAt (mem_of_superset
        (Metric.isOpen_ball.mem_nhds hy.1) Metric.ball_subset_closedBall))
      (fun y _ => hq.contDiffAt (x := y))
      (d := 6*η) (fun y _ => by
        simpa using (coordinateLaplacian_quadratic 0 y η).ge)
    have hadd' : WeakLaplacianLower v U (6*η) := by simpa [v] using hadd
    exact hadd'.mono (fun y hy => hsub (Metric.ball_subset_closedBall hy))
  exact no_maximum_of_strict_weakLaplacian_local hr (by positivity : 0 < 6*η)
    (hv.mono (fun y hy => Metric.ball_subset_closedBall (hsub hy).1)) hlocal
    (fun y hy => hxm (Metric.ball_subset_closedBall (hsub (Metric.ball_subset_closedBall hy)).1))

theorem aTF_pos : 0 < aTF := by
  have := kTF_pos
  unfold aTF
  positivity

theorem rpow_three_halves {x : ℝ} (hx : 0 ≤ x) :
    x^(3/2 : ℝ) = x*Real.sqrt x := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hx (by norm_num : (1:ℝ)+1/2 ≠ 0)]
  norm_num

theorem aTF_value : aTF = 81*Real.pi^2/8 := by
  have htwo : ((2:ℝ)^(3/2 : ℝ))^2 = 8 := by
    rw [rpow_three_halves (by norm_num : (0:ℝ)≤2), mul_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hk : kTF^2 = 8/(9*Real.pi^4) := by
    unfold kTF
    rw [div_pow, htwo]
    ring
  unfold aTF
  rw [div_pow, mul_pow, mul_pow, hk]
  field_simp
  ring

theorem profile_coefficient : kTF*aTF^(3/2 : ℝ) = 3*aTF/Real.pi := by
  have hk := kTF_pos
  rw [rpow_three_halves aTF_pos.le]
  have hs : Real.sqrt aTF = 12/(4*Real.pi*kTF) := by
    unfold aTF
    rw [Real.sqrt_sq (by positivity : (0:ℝ)≤12/(4*Real.pi*kTF))]
  rw [hs]
  field_simp [ne_of_gt hk]
  ring

theorem weak_sommerfeld_rigidity_exact {F : Position → ℝ} {B C : ℝ}
    (hB : 0 < B) (hF : ContinuousOn F punctured)
    (hw : HasWeakLaplacian F punctured (fun x => 4*Real.pi*kTF*F x^(3/2 : ℝ)))
    (hbounds : ∀ x ≠ 0, B/‖x‖^4 ≤ F x ∧ F x ≤ C/‖x‖^4) :
    ∀ x ≠ 0, F x = (81*Real.pi^2/8)/‖x‖^4 := by
  have hc : 0 < 4*Real.pi*kTF := by have := kTF_pos; positivity
  have hs : ∀ x ≠ 0, B ≤ scaledProfile F x ∧ scaledProfile F x ≤ C := by
    intro x hx
    have hp : 0 < ‖x‖^4 := pow_pos (norm_pos_iff.mpr hx) _
    have hl := (div_le_iff₀ hp).mp (hbounds x hx).1
    have hu := (le_div_iff₀ hp).mp (hbounds x hx).2
    constructor <;> dsimp [scaledProfile] <;> nlinarith
  intro x hx
  have he := weak_sommerfeld_rigidity hc hB hF hw hs x hx
  change F x = aTF*radialPower (-2) x at he
  rw [aTF_value] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  norm_num [radialPower, Real.rpow_neg_natCast, div_eq_mul_inv, ← pow_mul]

theorem WeakLaplacianGE.lower_on {f q : Position → ℝ} {U V : Set Position} {c : ℝ}
    (hw : WeakLaplacianGE f U q) (hV : V ⊆ U) (hq : LocallyIntegrableOn q U)
    (hl : ∀ x ∈ V, c ≤ q x) : WeakLaplacianLower f V c := by
  intro φ hφ hc ht hp
  have hiq : Integrable (fun x => q x*φ x) :=
    (integrableOn_iff_integrable_of_support_subset
      ((Function.support_mul_subset_right q φ).trans (subset_tsupport φ))).mp
      ((hq.integrableOn_compact_subset (ht.trans hV) hc).mul_continuousOn hφ.continuous.continuousOn hc)
  apply le_trans _ (hw φ hφ hc (ht.trans hV) hp)
  rw [← integral_const_mul]
  apply integral_mono ((hφ.continuous.integrable_of_hasCompactSupport hc).const_mul c) hiq
  intro x
  by_cases hx : x ∈ tsupport φ
  · exact mul_le_mul_of_nonneg_right (hl x (ht hx)) (hp x)
  · simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero, le_refl]

theorem weak_comparison_closedBall {u F L q : Position → ℝ} {c R : ℝ}
    (hR : 0 < R) (hc : 0 ≤ c)
    (hcont : ContinuousOn (fun x => u x-F x-L x-c) (Metric.closedBall 0 R))
    (hL : ∀ x ∈ Metric.ball 0 R, 0 ≤ L x)
    (hbdy : ∀ x : Position, ‖x‖ = R → u x-F x-L x-c ≤ 0)
    (hw : WeakLaplacianGE (fun x => u x-F x-L x-c) (Metric.ball 0 R) q)
    (hq : LocallyIntegrableOn q (Metric.ball 0 R))
    (hsign : ∀ x ∈ Metric.ball 0 R, F x < u x → 0 ≤ q x) :
    ∀ x ∈ Metric.closedBall 0 R, u x ≤ F x+L x+c := by
  have hw' : WeakLaplacianLower (fun x => u x-F x-L x-c)
      (Metric.ball 0 R ∩ {x | 0 < u x-F x-L x-c}) 0 :=
    hw.lower_on Set.inter_subset_left hq (fun x hx => hsign x hx.1 (by
      have := hL x hx.1
      have hp : 0 < u x-F x-L x-c := hx.2
      linarith))
  intro x hx
  have hh := weak_maximum_principle_closedBall hR hcont hbdy hw' x hx
  linarith

end NeutralAtom
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

theorem potential_le_inner_mass {ρ : Position → ℝ} {x : Position} {a : ℝ}
    (hρ : Integrable ρ) (hpos : ∀ y, 0 ≤ ρ y) (hx : x ≠ 0)
    (ha : a ≤ ‖x‖/2) (hsupp : ∀ y, a < ‖y‖ → ρ y = 0) :
    Integrable (fun y => coulombKernel (x-y)*ρ y) ∧
      potentialOf ρ x ≤ (2/‖x‖)*(∫ y, ρ y) := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hb := hρ.const_mul (2/‖x‖)
  have hdom : ∀ y, coulombKernel (x-y)*ρ y ≤ (2/‖x‖)*ρ y := by
    intro y
    by_cases hy : a < ‖y‖
    · simp [hsupp y hy]
    · have hh : ‖x‖/2 ≤ ‖x-y‖ := by
        have := norm_le_norm_sub_add x y
        linarith [le_of_not_gt hy]
      have hi := inv_anti₀ (half_pos hxpos) hh
      have heq : (‖x‖/2)⁻¹ = 2/‖x‖ := by ring
      rw [heq] at hi
      exact mul_le_mul_of_nonneg_right hi (hpos y)
  have hm : AEStronglyMeasurable (fun y => coulombKernel (x-y)*ρ y) volume :=
    ((measurable_coulombKernel.comp (measurable_const.sub measurable_id)).aestronglyMeasurable).mul
      hρ.aestronglyMeasurable
  have hi := hb.mono' hm (Filter.Eventually.of_forall (fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (coulombKernel_nonneg _) (hpos y))]
    exact hdom y))
  refine ⟨hi, (integral_mono hi hb hdom).trans_eq ?_⟩
  exact integral_const_mul _ _

theorem integral_exterior_inverse_sixth {a : ℝ} (ha : 0 < a) :
    (∫ x : Position in {x | a < ‖x‖}, (‖x‖^6)⁻¹) = 4*Real.pi/(3*a^3) := by
  rw [radial_integral_exterior (fun r => (r^6)⁻¹) ha.le]
  have heq : (∫ r : ℝ in Set.Ioi a, r^2*(r^6)⁻¹) =
      ∫ r : ℝ in Set.Ioi a, r^(-4 : ℝ) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hr0 : 0 < r := ha.trans hr
    change r^2*(r^6)⁻¹ = r^(-4 : ℝ)
    norm_num [Real.rpow_neg hr0.le]
    field_simp
  rw [heq, integral_Ioi_rpow_of_lt (by norm_num : (-4:ℝ)< -1) ha]
  norm_num
  ring

theorem integrable_exterior_inverse_sixth {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : Position => (‖x‖^6)⁻¹) {x | a < ‖x‖} := by
  rw [radial_integrable_exterior (fun r => (r^6)⁻¹) ha.le]
  refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-4:ℝ)< -1) ha).congr_fun ?_
    measurableSet_Ioi
  intro r hr
  have hr0 : 0 < r := ha.trans hr
  change r^(-4 : ℝ) = r^2*(r^6)⁻¹
  norm_num [Real.rpow_neg hr0.le]
  field_simp

theorem potentialOf_nonneg {ρ : Position → ℝ} (hρ : ∀ y, 0 ≤ ρ y) (x : Position) :
    0 ≤ potentialOf ρ x := integral_nonneg (fun y => mul_nonneg (coulombKernel_nonneg _) (hρ y))

theorem inner_potential_tendsto_zero {ρ : ℕ → Position → ℝ} {a : ℕ → ℝ}
    (hi : ∀ n, Integrable (ρ n)) (hp : ∀ n y, 0 ≤ ρ n y)
    (hsupp : ∀ n y, a n < ‖y‖ → ρ n y = 0)
    (ha : Tendsto a atTop (𝓝 0)) (hmass : Tendsto (fun n => ∫ y, ρ n y) atTop (𝓝 0))
    {x : Position} (hx : x ≠ 0) :
    Tendsto (fun n => potentialOf (ρ n) x) atTop (𝓝 0) := by
  have he := ha.eventually (gt_mem_nhds (half_pos (norm_pos_iff.mpr hx)))
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => potentialOf_nonneg (hp n) x))
    (he.mono (fun n hn => (potential_le_inner_mass (hi n) (hp n) hx hn.le (hsupp n)).2))
  simpa using hmass.const_mul (2/‖x‖)

theorem correctionDensity_nonneg (q a S : ℝ) (x : Position) :
    0 ≤ correctionDensity q a S x := by
  apply Set.indicator_nonneg
  intro y hy
  positivity

theorem correctionDensity_measurable (q a S : ℝ) : Measurable (correctionDensity q a S) := by
  apply Measurable.indicator
    (measurable_const.mul ((measurable_norm.pow_const 6).inv))
  exact (isClosed_le continuous_const continuous_norm).measurableSet.inter
    (isClosed_le continuous_norm continuous_const).measurableSet

theorem correctionDensity_le_exterior {q a S : ℝ} :
    correctionDensity q a S ≤ᵐ[volume]
      (fun y : Position => (q^8)⁻¹*({y : Position | a < ‖y‖}.indicator (fun y => (‖y‖^6)⁻¹) y)) := by
  have hsphere : ∀ᵐ y : Position, ‖y‖ ≠ a := by
    rw [ae_iff]
    convert Measure.addHaar_sphere volume (0 : Position) a using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext y
    simp
  filter_upwards [hsphere] with y hy
  by_cases he : a ≤ ‖y‖ ∧ ‖y‖ ≤ S
  · have hm : a < ‖y‖ := lt_of_le_of_ne he.1 hy.symm
    simp [correctionDensity, he, hm]
  · have hp : 0 ≤ ({y : Position | a < ‖y‖}.indicator (fun y => (‖y‖^6)⁻¹)) y := by
      apply Set.indicator_nonneg
      intro z hz
      positivity
    have he' : y ∉ {y : Position | a ≤ ‖y‖ ∧ ‖y‖ ≤ S} := he
    rw [correctionDensity, Set.indicator_of_notMem he']
    exact mul_nonneg (by positivity : 0 ≤ (q^8)⁻¹) hp

theorem correctionDensity_integrable_and_mass {q a S : ℝ} (ha : 0 < a) :
    Integrable (correctionDensity q a S) ∧
      (∫ y, correctionDensity q a S y) ≤ (q^8)⁻¹*(4*Real.pi/(3*a^3)) := by
  have hset : MeasurableSet {y : Position | a < ‖y‖} :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  have hb := ((integrable_exterior_inverse_sixth ha).integrable_indicator hset).const_mul (q^8)⁻¹
  have hi : Integrable (correctionDensity q a S) := hb.mono'
    (correctionDensity_measurable q a S).aestronglyMeasurable
    (correctionDensity_le_exterior.mono (fun y hy => by
      rw [Real.norm_eq_abs, abs_of_nonneg (correctionDensity_nonneg q a S y)]
      exact hy))
  refine ⟨hi, (integral_mono_ae hi hb correctionDensity_le_exterior).trans_eq ?_⟩
  rw [integral_const_mul, integral_indicator hset, integral_exterior_inverse_sixth ha]

theorem correctionDensity_mass_bound {q a S : ℝ} (hq : 0 < q) (ha : 1/(2*q) ≤ a) :
    (∫ y, correctionDensity q a S y) ≤ (32*Real.pi/3)*(q^5)⁻¹ := by
  have ha0 : 0 < a := (by positivity : 0 < 1/(2*q)).trans_le ha
  apply (correctionDensity_integrable_and_mass ha0).2.trans
  have hm : (1/(2*q))^3 ≤ a^3 := pow_le_pow_left₀ (by positivity) ha 3
  have hd : (a^3)⁻¹ ≤ ((1/(2*q))^3)⁻¹ := inv_anti₀ (by positivity) hm
  have hc : 0 ≤ (q^8)⁻¹*(4*Real.pi/3) := by positivity
  calc
    (q^8)⁻¹*(4*Real.pi/(3*a^3)) = ((q^8)⁻¹*(4*Real.pi/3))*(a^3)⁻¹ := by ring
    _ ≤ ((q^8)⁻¹*(4*Real.pi/3))*((1/(2*q))^3)⁻¹ := mul_le_mul_of_nonneg_left hd hc
    _ = (32*Real.pi/3)*(q^5)⁻¹ := by field_simp; ring

theorem correctionDensity_local_bound {q a S : ℝ} {x y : Position} (hx : x ≠ 0)
    (hy : y ∈ Metric.ball x (‖x‖/4)) :
    correctionDensity q a S y ≤ (q^8)⁻¹*((‖x‖/2)^6)⁻¹ := by
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hyd : ‖x-y‖ < ‖x‖/4 := by
    simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hy
  have hyl : ‖x‖/2 ≤ ‖y‖ := by linarith [norm_le_norm_sub_add x y]
  have hi : (‖y‖^6)⁻¹ ≤ ((‖x‖/2)^6)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hyl 6)
  by_cases he : a ≤ ‖y‖ ∧ ‖y‖ ≤ S
  · simpa [correctionDensity, he] using mul_le_mul_of_nonneg_left hi
      (by positivity : 0 ≤ (q^8)⁻¹)
  · have he' : y ∉ {y : Position | a ≤ ‖y‖ ∧ ‖y‖ ≤ S} := he
    rw [correctionDensity, Set.indicator_of_notMem he']
    positivity

theorem correction_potential_tendsto_zero {q a : ℕ → ℝ} (S : ℝ)
    (hq : Tendsto q atTop atTop) (ha : ∀ᶠ n in atTop, 1/(2*q n) ≤ a n)
    {x : Position} (hx : x ≠ 0) :
    Tendsto (fun n => potentialOf (correctionDensity (q n) (a n) S) x) atTop (𝓝 0) := by
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hq8 : Tendsto (fun n => ((q n)^8)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by decide : 8 ≠ 0)).comp hq)
  have hq5 : Tendsto (fun n => ((q n)^5)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by decide : 5 ≠ 0)).comp hq)
  have hbound : ∀ᶠ n in atTop, potentialOf (correctionDensity (q n) (a n) S) x ≤
      ((q n)^8)⁻¹*((‖x‖/2)^6)⁻¹*kernelBallMass (‖x‖/4)+
        (‖x‖/4)⁻¹*((32*Real.pi/3)*((q n)^5)⁻¹) := by
    filter_upwards [ha, hq.eventually (eventually_gt_atTop 0)] with n hn hqn
    have han : 0 < a n := (by positivity : 0 < 1/(2*q n)).trans_le hn
    apply (potential_integrable_and_bound (correctionDensity_integrable_and_mass han).1
      (correctionDensity_nonneg _ _ _) (by positivity)
      (fun y hy => correctionDensity_local_bound hx hy)).2.trans
    apply add_le_add le_rfl
    exact mul_le_mul_of_nonneg_left (correctionDensity_mass_bound hqn hn)
      (by positivity : 0 ≤ (‖x‖/4)⁻¹)
  apply squeeze_zero' (Filter.Eventually.of_forall
    (fun n => potentialOf_nonneg (correctionDensity_nonneg _ _ _) x)) hbound
  simpa using ((hq8.mul_const (((‖x‖/2)^6)⁻¹)).mul_const (kernelBallMass (‖x‖/4))).add
    ((hq5.const_mul (32*Real.pi/3)).const_mul (‖x‖/4)⁻¹)

theorem corrected_test_identity {U σ η φ : Position → ℝ} {lam c Aσ Aη : ℝ}
    (hU : Continuous (fun x => U x-lam*coulombKernel x))
    (hσ : Integrable σ) (hσpos : ∀ x, 0 ≤ σ x) (hσbd : ∀ x, σ x ≤ Aσ)
    (hη : Integrable η) (hηpos : ∀ x, 0 ≤ η x) (hηbd : ∀ x, η x ≤ Aη)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x, (U x-(lam*coulombKernel x-potentialOf σ x)-potentialOf η x-c)*coordinateLaplacian φ x) =
      (∫ x, U x*coordinateLaplacian φ x)+4*Real.pi*lam*φ 0-
        (∫ x, (4*Real.pi)*σ x*φ x)+(∫ x, (4*Real.pi)*η x*φ x) := by
  have hL : Continuous (coordinateLaplacian φ) :=
    continuous_coordinateLaplacian (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top))
  have hLc := hasCompactSupport_coordinateLaplacian hc
  have hiK : Integrable (fun x => coulombKernel x*coordinateLaplacian φ x) := by
    simpa only [smul_eq_mul] using
      locallyIntegrable_coulombKernel.integrable_smul_right_of_hasCompactSupport hL hLc
  have hiUreg : Integrable (fun x => (U x-lam*coulombKernel x)*coordinateLaplacian φ x) :=
    integrable_mul_compact_of_continuousAt (fun x _ => hU.continuousAt) hL hLc
  have hiU : Integrable (fun x => U x*coordinateLaplacian φ x) := by
    exact (hiUreg.add (hiK.const_mul lam)).congr (Filter.Eventually.of_forall (by
      intro x
      simp only [Pi.add_apply]
      ring))
  have hiσ : Integrable (fun x => potentialOf σ x*coordinateLaplacian φ x) :=
    integrable_mul_compact_of_continuousAt
      (fun _ _ => (potentialOf_continuous hσ hσpos hσbd).continuousAt) hL hLc
  have hiη : Integrable (fun x => potentialOf η x*coordinateLaplacian φ x) :=
    integrable_mul_compact_of_continuousAt
      (fun _ _ => (potentialOf_continuous hη hηpos hηbd).continuousAt) hL hLc
  have hilamK : Integrable (fun x => lam*coulombKernel x*coordinateLaplacian φ x) := by
    simpa only [mul_assoc] using hiK.const_mul lam
  have he : (fun x => (U x-(lam*coulombKernel x-potentialOf σ x)-potentialOf η x-c)*coordinateLaplacian φ x) =
      (fun x => (((U x*coordinateLaplacian φ x-lam*coulombKernel x*coordinateLaplacian φ x)+
        potentialOf σ x*coordinateLaplacian φ x)-potentialOf η x*coordinateLaplacian φ x)-c*coordinateLaplacian φ x) := by
    funext x
    ring
  have hii1 : Integrable (fun x => U x*coordinateLaplacian φ x-
      lam*coulombKernel x*coordinateLaplacian φ x) := hiU.sub hilamK
  have hii2 : Integrable (fun x => U x*coordinateLaplacian φ x-
      lam*coulombKernel x*coordinateLaplacian φ x+
      potentialOf σ x*coordinateLaplacian φ x) := hii1.add hiσ
  have hii3 : Integrable (fun x => U x*coordinateLaplacian φ x-
      lam*coulombKernel x*coordinateLaplacian φ x+
      potentialOf σ x*coordinateLaplacian φ x-
      potentialOf η x*coordinateLaplacian φ x) := hii2.sub hiη
  rw [he, integral_sub hii3
    ((hL.integrable_of_hasCompactSupport hLc).const_mul c),
    integral_sub hii2 hiη, integral_add hii1 hiσ, integral_sub hiU hilamK]
  have hσP := potentialOf_weakLaplacian hσ φ hφ hc (Set.subset_univ _)
  have hηP := potentialOf_weakLaplacian hη φ hφ hc (Set.subset_univ _)
  rw [hσP, hηP]
  simp_rw [show ∀ x, lam*coulombKernel x*coordinateLaplacian φ x =
    lam*(coulombKernel x*coordinateLaplacian φ x) by intro x; ring,
    integral_const_mul, integral_coulombKernel_laplacian hφ hc,
    integral_coordinateLaplacian hφ hc]
  simp only [neg_mul, integral_neg, mul_zero]
  ring

theorem cancel_nuclear_source {U σ η s q : Position → ℝ} {lam c Aσ Aη : ℝ}
    {Ω : Set Position} (hU : Continuous (fun x => U x-lam*coulombKernel x))
    (hσ : Integrable σ) (hσpos : ∀ x, 0 ≤ σ x) (hσbd : ∀ x, σ x ≤ Aσ)
    (hη : Integrable η) (hηpos : ∀ x, 0 ≤ η x) (hηbd : ∀ x, η x ≤ Aη)
    (hs : LocallyIntegrableOn s Ω) (hq : LocallyIntegrableOn q Ω)
    (hw : WeakNuclearSubsolution U lam Ω s)
    (hle : ∀ x ∈ Ω, q x ≤ s x-(4*Real.pi)*σ x+(4*Real.pi)*η x) :
    WeakLaplacianGE
      (fun x => U x-(lam*coulombKernel x-potentialOf σ x)-potentialOf η x-c) Ω q := by
  intro φ hφ hc ht hp
  have his := integrable_mul_test_on hs hφ.continuous hc ht
  have hiq := integrable_mul_test_on hq hφ.continuous hc ht
  have hiσ : Integrable (fun x => σ x*φ x) := by
    simpa only [smul_eq_mul] using
      hσ.locallyIntegrable.integrable_smul_right_of_hasCompactSupport hφ.continuous hc
  have hiη : Integrable (fun x => η x*φ x) := by
    simpa only [smul_eq_mul] using
      hη.locallyIntegrable.integrable_smul_right_of_hasCompactSupport hφ.continuous hc
  have hiσ' : Integrable (fun x => (4*Real.pi)*σ x*φ x) := by
    simpa only [mul_assoc] using hiσ.const_mul (4*Real.pi)
  have hiη' : Integrable (fun x => (4*Real.pi)*η x*φ x) := by
    simpa only [mul_assoc] using hiη.const_mul (4*Real.pi)
  have hle' : ∀ x, q x*φ x ≤ s x*φ x-(4*Real.pi)*σ x*φ x+(4*Real.pi)*η x*φ x := by
    intro x
    by_cases hx : x ∈ tsupport φ
    · have hh := mul_le_mul_of_nonneg_right (hle x (ht hx)) (hp x)
      nlinarith
    · simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero, sub_self, add_zero, le_refl]
  have hh := integral_mono hiq ((his.sub hiσ').add hiη') hle'
  simp only [Pi.add_apply, Pi.sub_apply] at hh
  have hisub : Integrable (fun x => s x*φ x-(4*Real.pi)*σ x*φ x) := his.sub hiσ'
  rw [integral_add hisub hiη', integral_sub his hiσ'] at hh
  rw [corrected_test_identity hU hσ hσpos hσbd hη hηpos hηbd hφ hc]
  have hw' := hw φ hφ hc ht hp
  linarith

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_TfReaction
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

theorem cutoffReaction_locallyIntegrable {a A : ℝ} {F : Position → ℝ}
    (hm : Measurable F) (hbd : ∀ x, a ≤ ‖x‖ → F x ≤ A) :
    LocallyIntegrable (cutoffReaction a F) := by
  have hmeas : Measurable (cutoffReaction a F) :=
    (tfReaction_continuous.measurable.comp hm).indicator
      (isClosed_le continuous_const continuous_norm).measurableSet
  apply (locallyIntegrable_const (tfReaction A)).mono hmeas.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : a ≤ ‖x‖
  · have hh := tfReaction_monotone (hbd x hx)
    simpa [cutoffReaction, hx, Real.norm_eq_abs,
      abs_of_nonneg (tfReaction_nonneg _)] using hh
  · simp [cutoffReaction, hx]

theorem screenedPotential_measurable {lam A : ℝ} {σ : Position → ℝ}
    (hσ : Integrable σ) (hσpos : ∀ x, 0 ≤ σ x) (hσbd : ∀ x, σ x ≤ A) :
    Measurable (screenedPotential lam σ) :=
  (measurable_const.mul measurable_coulombKernel).sub
    (potentialOf_continuous hσ hσpos hσbd).measurable

theorem screenedPotential_upper {lam a : ℝ} {σ : Position → ℝ}
    (ha : 0 < a) (hσpos : ∀ x, 0 ≤ σ x) {x : Position} (hx : a ≤ ‖x‖) :
    screenedPotential lam σ x ≤ |lam|/a := by
  have hK : 0 ≤ coulombKernel x := coulombKernel_nonneg x
  have hKa : coulombKernel x ≤ a⁻¹ := inv_anti₀ ha hx
  have hp := potentialOf_nonneg hσpos x
  dsimp [screenedPotential]
  calc
    lam*coulombKernel x-potentialOf σ x ≤ lam*coulombKernel x := sub_le_self _ hp
    _ ≤ |lam| *coulombKernel x := mul_le_mul_of_nonneg_right (le_abs_self _) hK
    _ ≤ |lam| *a⁻¹ := mul_le_mul_of_nonneg_left hKa (abs_nonneg _)
    _ = _ := by rw [div_eq_mul_inv]

theorem barrier_difference_weakGE {U σ p e : Position → ℝ}
    {lam a S c AU Aσ Ap Ae : ℝ} (ha : 0 < a)
    (hU : Continuous (fun x => U x-lam*coulombKernel x))
    (hUbd : ∀ x, a ≤ ‖x‖ → U x ≤ AU)
    (hσ : Integrable σ) (hσpos : ∀ x, 0 ≤ σ x) (hσbd : ∀ x, σ x ≤ Aσ)
    (hp : Integrable p) (hppos : ∀ x, 0 ≤ p x) (hpbd : ∀ x, p x ≤ Ap)
    (he : Integrable e) (hepos : ∀ x, 0 ≤ e x) (hebd : ∀ x, e x ≤ Ae)
    (hw : WeakNuclearSubsolution U lam (Metric.ball 0 S) (barrierSource a U σ p))
    (hband : ∀ x ∈ Metric.ball (0 : Position) S, a ≤ ‖x‖ →
      (4*Real.pi)*σ x ≤ tfReaction (screenedPotential lam σ x)+(4*Real.pi)*e x) :
    WeakLaplacianGE
      (fun x => U x-screenedPotential lam σ x-potentialOf (fun y => p y+e y) x-c)
      (Metric.ball 0 S) (fun x => cutoffReaction a U x-cutoffReaction a (screenedPotential lam σ) x) := by
  have hmU : Measurable U := by
    have hm : Measurable (fun x => U x-lam*coulombKernel x+lam*coulombKernel x) :=
      hU.measurable.add (measurable_coulombKernel.const_mul lam)
    simpa only [sub_add_cancel] using hm
  have hiU := cutoffReaction_locallyIntegrable hmU hUbd
  have hiF := cutoffReaction_locallyIntegrable
    (screenedPotential_measurable (lam := lam) hσ hσpos hσbd)
    (fun x hx => screenedPotential_upper ha hσpos hx)
  have hiσ : LocallyIntegrable (fun x => (4*Real.pi)*({x : Position | ‖x‖ < a}.indicator σ) x) :=
    (hσ.locallyIntegrable.indicator
      (isOpen_lt continuous_norm continuous_const).measurableSet).smul (4*Real.pi)
  have his : LocallyIntegrable (barrierSource a U σ p) :=
    (hiσ.sub (hp.locallyIntegrable.smul (4*Real.pi))).add hiU
  apply cancel_nuclear_source hU hσ hσpos hσbd
    (hp.add he) (fun x => add_nonneg (hppos x) (hepos x))
    (fun x => add_le_add (hpbd x) (hebd x))
    (his.locallyIntegrableOn _) ((hiU.sub hiF).locallyIntegrableOn _) hw
  intro x hx
  change cutoffReaction a U x-cutoffReaction a (screenedPotential lam σ) x ≤
    barrierSource a U σ p x-(4*Real.pi)*σ x+(4*Real.pi)*(p x+e x)
  by_cases hin : ‖x‖ < a
  · simp only [barrierSource, cutoffReaction, Set.indicator, Set.mem_ofPred_eq,
      ite_eq_left hin, ite_eq_right (not_le.mpr hin), sub_self]
    have he0 := hepos x
    nlinarith [Real.pi_pos]
  · have hout : a ≤ ‖x‖ := le_of_not_gt hin
    have hh := hband x hx hout
    simp only [barrierSource, cutoffReaction, Set.indicator, Set.mem_ofPred_eq,
      ite_eq_right hin, ite_eq_left hout, mul_zero]
    linarith

theorem positive_barrier_comparison {U σ p e : Position → ℝ}
    {lam a S c AU Aσ Ap Ae : ℝ} (ha : 0 < a) (hS : 0 < S) (hc : 0 ≤ c)
    (hU : Continuous (fun x => U x-lam*coulombKernel x))
    (hUbd : ∀ x, a ≤ ‖x‖ → U x ≤ AU)
    (hσ : Integrable σ) (hσpos : ∀ x, 0 ≤ σ x) (hσbd : ∀ x, σ x ≤ Aσ)
    (hp : Integrable p) (hppos : ∀ x, 0 ≤ p x) (hpbd : ∀ x, p x ≤ Ap)
    (he : Integrable e) (hepos : ∀ x, 0 ≤ e x) (hebd : ∀ x, e x ≤ Ae)
    (hw : WeakNuclearSubsolution U lam (Metric.ball 0 S) (barrierSource a U σ p))
    (hband : ∀ x ∈ Metric.ball (0 : Position) S, a ≤ ‖x‖ →
      (4*Real.pi)*σ x ≤ tfReaction (screenedPotential lam σ x)+(4*Real.pi)*e x)
    (hbdy : ∀ x : Position, ‖x‖ = S →
      U x-screenedPotential lam σ x-potentialOf (fun y => p y+e y) x-c ≤ 0) :
    ∀ x ∈ Metric.closedBall (0 : Position) S,
      U x ≤ screenedPotential lam σ x+potentialOf (fun y => p y+e y) x+c := by
  have hmU : Measurable U := by
    have hm : Measurable (fun x => U x-lam*coulombKernel x+lam*coulombKernel x) :=
      hU.measurable.add (measurable_coulombKernel.const_mul lam)
    simpa only [sub_add_cancel] using hm
  have hiU := cutoffReaction_locallyIntegrable hmU hUbd
  have hiF := cutoffReaction_locallyIntegrable
    (screenedPotential_measurable (lam := lam) hσ hσpos hσbd)
    (fun x hx => screenedPotential_upper ha hσpos hx)
  have hη := hp.add he
  have hηpos : ∀ x, 0 ≤ p x+e x := fun x => add_nonneg (hppos x) (hepos x)
  have hηbd : ∀ x, p x+e x ≤ Ap+Ae := fun x => add_le_add (hpbd x) (hebd x)
  have hcont : Continuous (fun x => U x-screenedPotential lam σ x-
      potentialOf (fun y => p y+e y) x-c) := by
    have hh := ((hU.add (potentialOf_continuous hσ hσpos hσbd)).sub
      (potentialOf_continuous hη hηpos hηbd)).sub (continuous_const (y := c))
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    change U x-(lam*coulombKernel x-potentialOf σ x)-potentialOf (p+e) x-c =
      U x-lam*coulombKernel x+potentialOf σ x-potentialOf (p+e) x-c
    ring
  apply weak_comparison_closedBall hS hc hcont.continuousOn
    (fun x _ => potentialOf_nonneg hηpos x) hbdy
    (barrier_difference_weakGE ha hU hUbd hσ hσpos hσbd
      hp hppos hpbd he hepos hebd hw hband) ((hiU.sub hiF).locallyIntegrableOn _)
  intro x _ hx
  by_cases hax : a ≤ ‖x‖
  · simp only [cutoffReaction, Set.indicator, Set.mem_ofPred_eq, ite_eq_left hax]
    exact sub_nonneg.mpr (tfReaction_monotone hx.le)
  · simp [cutoffReaction, hax]

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_HarmonicInterior
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
noncomputable section
namespace NeutralAtom
theorem dirPartial_mul {f g : Position → ℝ} {x v : Position}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    dirPartial (fun y => f y*g y) v x = f x*dirPartial g v x+g x*dirPartial f v x := by
  change fderiv ℝ (f*g) x v = _
  rw [fderiv_mul hf hg]
  simp [dirPartial]

theorem dirPartial_add {f g : Position → ℝ} {x v : Position}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    dirPartial (fun y => f y+g y) v x = dirPartial f v x+dirPartial g v x := by
  change fderiv ℝ (f+g) x v = _
  rw [fderiv_add hf hg]
  rfl

theorem coordinateLaplacian_mul {f g : Position → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : Position) :
    coordinateLaplacian (fun y => f y*g y) x =
      f x*coordinateLaplacian g x+g x*coordinateLaplacian f x+
        2*∑ a : Fin 3, dirPartial f (axis a) x*dirPartial g (axis a) x := by
  have hf1 := hf.differentiable (by norm_num)
  have hg1 := hg.differentiable (by norm_num)
  have hpf (a) : Differentiable ℝ (dirPartial f (axis a)) :=
    (contDiff_partial (n := 1) hf (axis a)).differentiable (by norm_num)
  have hpg (a) : Differentiable ℝ (dirPartial g (axis a)) :=
    (contDiff_partial (n := 1) hg (axis a)).differentiable (by norm_num)
  rw [coordinateLaplacian_eq_partials (hf.mul hg).contDiffAt,
    coordinateLaplacian_eq_partials hg.contDiffAt,
    coordinateLaplacian_eq_partials hf.contDiffAt]
  have hh (a : Fin 3) : dirPartial (dirPartial (fun y => f y*g y) (axis a)) (axis a) x =
      f x*dirPartial (dirPartial g (axis a)) (axis a) x+
      g x*dirPartial (dirPartial f (axis a)) (axis a) x+
      2*(dirPartial f (axis a) x*dirPartial g (axis a) x) := by
    have heq : dirPartial (fun y => f y*g y) (axis a) =
        fun y => f y*dirPartial g (axis a) y+g y*dirPartial f (axis a) y :=
      funext (fun y => dirPartial_mul (hf1 y) (hg1 y))
    rw [heq, dirPartial_add
      (f := fun y => f y*dirPartial g (axis a) y)
      (g := fun y => g y*dirPartial f (axis a) y)
      (by simpa only [Pi.mul_def] using (hf1 x).mul (hpg a x))
      (by simpa only [Pi.mul_def] using (hg1 x).mul (hpf a x)),
      dirPartial_mul (hf1 x) (hpg a x), dirPartial_mul (hg1 x) (hpf a x)]
    ring
  simp_rw [hh, Finset.sum_add_distrib, Finset.mul_sum]

theorem regularizedPartial_tendsto {ε : ℕ → ℝ} (hε : ∀ n, ε n ≠ 0)
    (hlim : Tendsto ε atTop (𝓝 0)) (a : Fin 3) {x : Position} (hx : x ≠ 0) :
    Tendsto (fun n => dirPartial (regularizedKernel (ε n)) (axis a) x)
      atTop (𝓝 (coulombPartial a x)) := by
  simp only [dirPartial_regularizedKernel (hε _)]
  have hh : Tendsto (fun n => ‖x‖^2+(ε n)^2) atTop (𝓝 (‖x‖^2)) := by
    simpa using tendsto_const_nhds.add (hlim.pow 2)
  exact tendsto_const_nhds.mul (hh.rpow_const (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))))

theorem dirPartial_regularizedKernel_bound {ε : ℝ} (hε : ε ≠ 0)
    (a : Fin 3) {x : Position} (hx : x ≠ 0) :
    ‖dirPartial (regularizedKernel ε) (axis a) x‖ ≤ (coulombKernel x)^2 := by
  rw [dirPartial_regularizedKernel hε]
  simp only [norm_mul, norm_neg, Real.norm_eq_abs]
  rw [abs_of_nonneg (Real.rpow_nonneg (add_nonneg (sq_nonneg ‖x‖) (sq_nonneg ε)) (-3/2 : ℝ))]
  have hnorm : |x a| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x a
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hr : (‖x‖^2+ε^2)^(-3/2 : ℝ) ≤ (‖x‖^2)^(-3/2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg ε]) (by norm_num)
  have he : ‖x‖*(‖x‖^2)^(-3/2 : ℝ) = (coulombKernel x)^2 := by
    rw [← Real.rpow_natCast_mul (norm_nonneg x)]
    norm_num [Real.rpow_neg hpos.le, coulombKernel]
    field_simp
  exact (mul_le_mul hnorm hr (by positivity) (norm_nonneg x)).trans_eq he

theorem locallyIntegrable_coulombKernel_sq :
    LocallyIntegrable (fun x => (coulombKernel x)^2) volume := by
  intro x
  refine ⟨Metric.ball 0 (‖x‖+1), IsOpen.mem_nhds Metric.isOpen_ball ?_,
    coulombKernel_sq_integrableOn_ball _⟩
  simpa only [Metric.mem_ball, dist_zero_right] using lt_add_one ‖x‖

theorem regularizedPartial_integral_tendsto {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    (a : Fin 3) {φ : Position → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Tendsto (fun n => ∫ x, dirPartial (regularizedKernel (ε n)) (axis a) x*φ x)
      atTop (𝓝 (∫ x, coulombPartial a x*φ x)) := by
  have hae : ∀ᵐ x : Position ∂volume, x ≠ 0 := volume.ae_ne 0
  have hb : Integrable (fun x => (coulombKernel x)^2*‖φ x‖) := by
    simpa only [smul_eq_mul] using
      locallyIntegrable_coulombKernel_sq.integrable_smul_right_of_hasCompactSupport hφ.norm hφc.norm
  apply tendsto_integral_of_dominated_convergence (fun x => (coulombKernel x)^2*‖φ x‖)
  · intro n
    exact ((contDiff_partial (n := ∞) (by simpa using contDiff_regularizedKernel (hε n).ne')
      (axis a)).continuous.mul hφ).aestronglyMeasurable
  · exact hb
  · intro n
    filter_upwards [hae] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (dirPartial_regularizedKernel_bound (hε n).ne' a hx)
      (norm_nonneg _)
  · filter_upwards [hae] with x hx
    exact (regularizedPartial_tendsto (fun n => (hε n).ne') hlim a hx).mul_const (φ x)

theorem weak_harmonic_reproduction {h χ : Position → ℝ} {U : Set Position}
    (hh : Continuous h) (hharm : HasWeakLaplacian h U (fun _ => 0))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) :
    (∫ x, coulombKernel x*(h x*coordinateLaplacian χ x)) +
      2*∑ a : Fin 3, ∫ x, coulombPartial a x*(h x*dirPartial χ (axis a) x) =
      4*Real.pi*(h 0*χ 0) := by
  let ε : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have hε : ∀ n, 0 < ε n := fun n => by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hχ2 : ContDiff ℝ 2 χ := hχ.of_le (by exact WithTop.coe_le_coe.mpr le_top)
  have hcdelta : Continuous (coordinateLaplacian χ) := continuous_coordinateLaplacian hχ2
  have hcsdelta : HasCompactSupport (coordinateLaplacian χ) :=
    hasCompactSupport_coordinateLaplacian hχc
  have hcp (a : Fin 3) : ContDiff ℝ ∞ (dirPartial χ (axis a)) :=
    contDiff_partial (by simpa using hχ) (axis a)
  have hcsp (a : Fin 3) := hasCompactSupport_partial hχc (axis a)
  have hn (n : ℕ) :
      (∫ x, regularizedKernel (ε n) x*(h x*coordinateLaplacian χ x)) +
        2*∑ a : Fin 3, ∫ x, dirPartial (regularizedKernel (ε n)) (axis a) x*
          (h x*dirPartial χ (axis a) x) =
        ∫ x, regularizedCharge (ε n) x*(h x*χ x) := by
    have hK := contDiff_regularizedKernel (hε n).ne'
    have hK2 : ContDiff ℝ 2 (regularizedKernel (ε n)) :=
      hK.of_le (by exact WithTop.coe_le_coe.mpr le_top)
    have hpK (a : Fin 3) : Continuous (dirPartial (regularizedKernel (ε n)) (axis a)) :=
      (contDiff_partial (n := ∞) (by simpa using hK) (axis a)).continuous
    have hq : Continuous (regularizedCharge (ε n)) := by
      have heq : regularizedCharge (ε n) = fun x => -coordinateLaplacian (regularizedKernel (ε n)) x := by
        ext x
        rw [laplacian_regularizedKernel (hε n).ne']
        ring
      rw [heq]
      exact (continuous_coordinateLaplacian hK2).neg
    have hiK : Integrable (fun x => regularizedKernel (ε n) x*(h x*coordinateLaplacian χ x)) :=
      (hK.continuous.mul (hh.mul hcdelta)).integrable_of_hasCompactSupport
        (hcsdelta.mul_left.mul_left)
    have hiq : Integrable (fun x => regularizedCharge (ε n) x*(h x*χ x)) :=
      (hq.mul (hh.mul hχ.continuous)).integrable_of_hasCompactSupport (hχc.mul_left.mul_left)
    have hip (a : Fin 3) : Integrable (fun x => dirPartial (regularizedKernel (ε n)) (axis a) x*
        (h x*dirPartial χ (axis a) x)) :=
      ((hpK a).mul (hh.mul (hcp a).continuous)).integrable_of_hasCompactSupport
        ((hcsp a).mul_left.mul_left)
    have he := hharm (fun x => χ x*regularizedKernel (ε n) x) (hχ.mul hK)
      hχc.mul_right (by exact (closure_mono (Function.support_mul_subset_left _ _)).trans hχU)
    have heq : (fun x => h x*coordinateLaplacian (fun y => χ y*regularizedKernel (ε n) y) x) =
        fun x => (regularizedKernel (ε n) x*(h x*coordinateLaplacian χ x)-
          regularizedCharge (ε n) x*(h x*χ x)) +
          2*∑ a : Fin 3, dirPartial (regularizedKernel (ε n)) (axis a) x*
              (h x*dirPartial χ (axis a) x) := by
      ext x
      rw [coordinateLaplacian_mul hχ2 hK2, laplacian_regularizedKernel (hε n).ne']
      simp only [Fin.sum_univ_three]
      ring
    have hisub : Integrable (fun x => regularizedKernel (ε n) x*(h x*coordinateLaplacian χ x)-
        regularizedCharge (ε n) x*(h x*χ x)) := by
      simpa only [Pi.sub_def] using hiK.sub hiq
    have hisum : Integrable (fun x => 2*∑ a : Fin 3,
        dirPartial (regularizedKernel (ε n)) (axis a) x*(h x*dirPartial χ (axis a) x)) :=
      (integrable_finsetSum Finset.univ (fun a _ => hip a)).const_mul 2
    rw [heq, integral_add hisub hisum,
      integral_sub hiK hiq, integral_const_mul, integral_finsetSum _ (fun a _ => hip a)] at he
    simp only [zero_mul, integral_zero] at he
    linarith
  have h1 := regularizedKernel_integral_tendsto hε hεlim (hh.mul hcdelta) hcsdelta.mul_left
  have h2 := tendsto_finsetSum Finset.univ (fun a _ =>
    regularizedPartial_integral_tendsto hε hεlim a (hh.mul (hcp a).continuous) (hcsp a).mul_left)
  have h3 := regularizedCharge_tendsto_dirac hε hεlim (hh.mul hχ.continuous) hχc.mul_left
  exact tendsto_nhds_unique ((h1.add (h2.const_mul 2)).congr' (Filter.Eventually.of_forall hn)) h3

theorem contDiffAt_coulombKernel {x : Position} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ coulombKernel x := by
  have he : coulombKernel = fun x : Position => (‖x‖^2)^(-1/2 : ℝ) :=
    funext coulombKernel_eq_rpow
  rw [he]
  exact (contDiff_norm_sq ℝ).contDiffAt.rpow_const_of_ne
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))

theorem contDiffAt_coulombPartial (a : Fin 3) {x : Position} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (coulombPartial a) x := by
  exact (EuclideanSpace.proj a).contDiff.contDiffAt.neg.mul
    ((contDiff_norm_sq ℝ).contDiffAt.rpow_const_of_ne (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)))

theorem cutoffHarmonicKernel_eq_zero_of_eventually_const {χ : Position → ℝ} {x : Position}
    {c : ℝ} (hχ : χ =ᶠ[𝓝 x] fun _ => c) : cutoffHarmonicKernel χ x = 0 := by
  have hdelta : coordinateLaplacian χ x = 0 := by
    rw [coordinateLaplacian_congr_nhds hχ]
    simp [coordinateLaplacian]
  have hp (a : Fin 3) : dirPartial χ (axis a) x = 0 := by
    unfold dirPartial
    rw [hχ.fderiv_eq]
    simp
  simp [cutoffHarmonicKernel, hdelta, hp]

theorem hasCompactSupport_cutoffHarmonicKernel {χ : Position → ℝ}
    (hχc : HasCompactSupport χ) : HasCompactSupport (cutoffHarmonicKernel χ) := by
  apply hχc.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (isClosed_tsupport χ)
  intro x hx
  by_contra h
  exact hx (cutoffHarmonicKernel_eq_zero_of_eventually_const
    (notMem_tsupport_iff_eventuallyEq.mp h))

theorem contDiff_cutoffHarmonicKernel {χ : Position → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ =ᶠ[𝓝 (0 : Position)] fun _ => (1 : ℝ)) :
    ContDiff ℝ ∞ (cutoffHarmonicKernel χ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    have he : cutoffHarmonicKernel χ =ᶠ[𝓝 (0 : Position)] fun _ => (0 : ℝ) := by
      filter_upwards [hχ0.eventually_nhds] with x hx
      exact cutoffHarmonicKernel_eq_zero_of_eventually_const hx
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hp (a : Fin 3) : ContDiffAt ℝ ∞ (dirPartial χ (axis a)) x :=
      (contDiff_partial (n := ∞) (by simpa using hχ) (axis a)).contDiffAt
    apply ContDiffAt.div_const
    apply ContDiffAt.add
    · exact (contDiffAt_coulombKernel hx).mul (contDiff_coordinateLaplacian hχ).contDiffAt
    · apply contDiffAt_const.mul
      apply ContDiffAt.sum
      intro a _
      exact (contDiffAt_coulombPartial a hx).mul (hp a)

theorem coulombPartial_bound (a : Fin 3) (x : Position) :
    ‖coulombPartial a x‖ ≤ (coulombKernel x)^2 := by
  by_cases hx : x = 0
  · subst x
    simp [coulombPartial, coulombKernel]
  · have hε : ∀ n : ℕ, ((n:ℝ)+1)⁻¹ ≠ 0 := fun n => by positivity
    have hlim : Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹) atTop (𝓝 (0 : ℝ)) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    exact le_of_tendsto (regularizedPartial_tendsto hε hlim a hx).norm
      (Filter.Eventually.of_forall (fun n => dirPartial_regularizedKernel_bound (hε n) a hx))

theorem measurable_coulombPartial (a : Fin 3) : Measurable (coulombPartial a) := by
  exact (EuclideanSpace.proj a).continuous.measurable.neg.mul
    ((continuous_norm.measurable.pow_const (2 : ℕ)).pow_const (-3/2 : ℝ))

theorem coulombPartial_integrable_mul_compact (a : Fin 3) {φ : Position → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Integrable (fun x => coulombPartial a x*φ x) := by
  have hb : Integrable (fun x => (coulombKernel x)^2*‖φ x‖) := by
    simpa only [smul_eq_mul] using
      locallyIntegrable_coulombKernel_sq.integrable_smul_right_of_hasCompactSupport hφ.norm hφc.norm
  apply hb.mono' ((measurable_coulombPartial a).aestronglyMeasurable.mul hφ.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun x => by
    change ‖coulombPartial a x*φ x‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (coulombPartial_bound a x) (norm_nonneg _))

theorem weak_harmonic_reproduction_kernel {h χ : Position → ℝ} {U : Set Position}
    (hh : Continuous h) (hharm : HasWeakLaplacian h U (fun _ => 0))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)
    (hχone : χ 0 = 1) :
    (∫ x, cutoffHarmonicKernel χ x*h x) = h 0 := by
  have hcdelta := (contDiff_coordinateLaplacian hχ).continuous
  have hcsdelta := hasCompactSupport_coordinateLaplacian hχc
  have hcp (a : Fin 3) : Continuous (dirPartial χ (axis a)) :=
    (contDiff_partial (n := ∞) (by simpa using hχ) (axis a)).continuous
  have hcsp (a : Fin 3) := hasCompactSupport_partial hχc (axis a)
  have hiK : Integrable (fun x => coulombKernel x*(h x*coordinateLaplacian χ x)) := by
    simpa only [smul_eq_mul, Pi.mul_apply] using
      locallyIntegrable_coulombKernel.integrable_smul_right_of_hasCompactSupport
        (hh.mul hcdelta) hcsdelta.mul_left
  have hip (a : Fin 3) : Integrable (fun x => coulombPartial a x*(h x*dirPartial χ (axis a) x)) :=
    coulombPartial_integrable_mul_compact a (hh.mul (hcp a)) (hcsp a).mul_left
  have hisum : Integrable (fun x => 2*∑ a : Fin 3, coulombPartial a x*(h x*dirPartial χ (axis a) x)) :=
    (integrable_finsetSum Finset.univ (fun a _ => hip a)).const_mul 2
  have heq : (fun x => cutoffHarmonicKernel χ x*h x) = fun x =>
      (4*Real.pi)⁻¹*((coulombKernel x*(h x*coordinateLaplacian χ x))+
      2*∑ a : Fin 3, coulombPartial a x*(h x*dirPartial χ (axis a) x)) := by
    ext x
    simp only [cutoffHarmonicKernel, Fin.sum_univ_three]
    ring
  rw [heq, integral_const_mul, integral_add hiK hisum, integral_const_mul,
    integral_finsetSum _ (fun a _ => hip a), weak_harmonic_reproduction hh hharm hχ hχc hχU, hχone]
  field_simp

theorem coordinateLaplacian_sub_right (φ : Position → ℝ) (x z : Position) :
    coordinateLaplacian (fun y => φ (y-z)) x = coordinateLaplacian φ (x-z) := by
  unfold coordinateLaplacian
  apply Finset.sum_congr rfl
  intro a _
  have he : (fun t : ℝ => φ ((x+t • axis a)-z)) = fun t => φ ((x-z)+t • axis a) := by
    ext t
    congr 1
    abel
  rw [he]

theorem HasWeakLaplacian.translate {h q : Position → ℝ} {U : Set Position}
    (hh : HasWeakLaplacian h U q) (z : Position) :
    HasWeakLaplacian (fun x => h (z+x)) {x | z+x ∈ U} (fun x => q (z+x)) := by
  intro φ hφ hφc hφU
  have hc : ContDiff ℝ ∞ (fun y => φ (y-z)) := hφ.comp (contDiff_id.sub contDiff_const)
  have hcs : HasCompactSupport (fun y => φ (y-z)) :=
    hφc.comp_homeomorph (Homeomorph.subRight z)
  have hs : tsupport (fun y => φ (y-z)) ⊆ U := by
    have hsub := tsupport_comp_subset_preimage φ (show Continuous (fun y : Position => y-z) by fun_prop)
    intro y hy
    have hy' : y-z ∈ tsupport φ := hsub hy
    have hh' := hφU hy'
    change z+(y-z) ∈ U at hh'
    rw [show z+(y-z) = y by abel] at hh'
    exact hh'
  have he := hh (fun y => φ (y-z)) hc hcs hs
  simp_rw [coordinateLaplacian_sub_right] at he
  have hl := integral_add_left_eq_self (μ := volume) (fun y => h y*coordinateLaplacian φ (y-z)) z
  have hr := integral_add_left_eq_self (μ := volume) (fun y => q y*φ (y-z)) z
  simpa only [add_sub_cancel_left] using hl.trans (he.trans hr.symm)

theorem weak_harmonic_reproduction_at {h χ : Position → ℝ} {U : Set Position}
    (hh : Continuous h) (hharm : HasWeakLaplacian h U (fun _ => 0))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχone : χ 0 = 1)
    {z : Position} (hχU : ∀ x ∈ tsupport χ, z+x ∈ U) :
    (∫ x, cutoffHarmonicKernel χ (x-z)*h x) = h z := by
  have he := weak_harmonic_reproduction_kernel
    (hh.comp (show Continuous (fun x : Position => z+x) by fun_prop))
    (hharm.translate z) hχ hχc hχU hχone
  have hl := integral_add_left_eq_self (μ := volume) (fun x => cutoffHarmonicKernel χ (x-z)*h x) z
  simp only [add_sub_cancel_left] at hl
  simpa only [Function.comp_apply, add_zero] using hl.symm.trans he

theorem harmonic_value_bound {h χ : Position → ℝ} {U W : Set Position} {M : ℝ}
    (hh : Continuous h) (hharm : HasWeakLaplacian h U (fun _ => 0))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχone : χ 0 = 1)
    (hW : IsCompact W) (hM : ∀ x, ‖cutoffHarmonicKernel χ x‖ ≤ M)
    {z : Position} (hχU : ∀ x ∈ tsupport χ, z+x ∈ U)
    (hχW : ∀ x ∈ tsupport χ, z+x ∈ W) :
    ‖h z‖ ≤ M*(∫ x in W, ‖h x‖) := by
  have hzero : ∀ x, x ∉ W → cutoffHarmonicKernel χ (x-z)*h x = 0 := by
    intro x hx
    have hh' : x-z ∉ tsupport χ := by
      intro hm
      have he := hχW (x-z) hm
      rw [show z+(x-z)=x by abel] at he
      exact hx he
    rw [cutoffHarmonicKernel_eq_zero_of_eventually_const
      (notMem_tsupport_iff_eventuallyEq.mp hh'), zero_mul]
  rw [← weak_harmonic_reproduction_at hh hharm hχ hχc hχone hχU,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hi : IntegrableOn (fun x => M * ‖h x‖) W volume :=
    (hh.norm.continuousOn.integrableOn_compact hW).const_mul M
  have hb := norm_integral_le_of_norm_le
    (f := fun x => cutoffHarmonicKernel χ (x-z)*h x) hi
    (Filter.Eventually.of_forall (fun x => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hM (x-z)) (norm_nonneg _)))
  simpa only [integral_const_mul] using hb

theorem harmonic_difference_bound {h χ : Position → ℝ} {U W : Set Position} {L : NNReal}
    (hh : Continuous h) (hharm : HasWeakLaplacian h U (fun _ => 0))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχ0 : χ =ᶠ[𝓝 (0 : Position)] fun _ => (1 : ℝ)) (hW : IsCompact W)
    (hL : LipschitzWith L (cutoffHarmonicKernel χ))
    {z z' : Position} (hχU : ∀ x ∈ tsupport χ, z+x ∈ U)
    (hχU' : ∀ x ∈ tsupport χ, z'+x ∈ U)
    (hχW : ∀ x ∈ tsupport χ, z+x ∈ W)
    (hχW' : ∀ x ∈ tsupport χ, z'+x ∈ W) :
    ‖h z-h z'‖ ≤ (L:ℝ)*(∫ x in W, ‖h x‖)*‖z-z'‖ := by
  have hcQ := (contDiff_cutoffHarmonicKernel hχ hχ0).continuous
  have hi (v : Position) : IntegrableOn (fun x => cutoffHarmonicKernel χ (x-v)*h x) W :=
    ((hcQ.comp (show Continuous (fun x : Position => x-v) by fun_prop)).mul hh).continuousOn.integrableOn_compact hW
  have hrepro (v : Position) (hvU : ∀ x ∈ tsupport χ, v+x ∈ U)
      (hvW : ∀ x ∈ tsupport χ, v+x ∈ W) :
      (∫ x in W, cutoffHarmonicKernel χ (x-v)*h x) = h v := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact weak_harmonic_reproduction_at hh hharm hχ hχc hχ0.eq_of_nhds hvU
    · intro x hx
      have hh' : x-v ∉ tsupport χ := by
        intro hm
        have he := hvW (x-v) hm
        rw [show v+(x-v)=x by abel] at he
        exact hx he
      rw [cutoffHarmonicKernel_eq_zero_of_eventually_const
        (notMem_tsupport_iff_eventuallyEq.mp hh'), zero_mul]
  rw [← hrepro z hχU hχW, ← hrepro z' hχU' hχW', ← integral_sub (hi z) (hi z')]
  have hb : ∀ x, ‖cutoffHarmonicKernel χ (x-z)*h x-cutoffHarmonicKernel χ (x-z')*h x‖ ≤
      ((L:ℝ)*‖z-z'‖)*‖h x‖ := by
    intro x
    rw [← sub_mul, norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have he := hL.norm_sub_le (x-z) (x-z')
    simpa only [show (x-z)-(x-z')=z'-z by abel, norm_sub_rev z' z] using he
  have hibound : IntegrableOn (fun x => ((L:ℝ)*‖z-z'‖)*‖h x‖) W volume :=
    (hh.norm.continuousOn.integrableOn_compact hW).const_mul _
  have hbound := norm_integral_le_of_norm_le hibound
    (Filter.Eventually.of_forall hb)
  rw [integral_const_mul] at hbound
  convert hbound using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem harmonic_interior_estimates {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : Position) (h : Position → ℝ), Continuous h →
      HasWeakLaplacian h (Metric.ball c (2*r)) (fun _ => 0) →
      (∀ z ∈ Metric.closedBall c r, ‖h z‖ ≤ C*(∫ x in Metric.closedBall c (2*r), ‖h x‖)) ∧
      (∀ z ∈ Metric.closedBall c r, ∀ z' ∈ Metric.closedBall c r,
        ‖h z-h z'‖ ≤ C*(∫ x in Metric.closedBall c (2*r), ‖h x‖)*‖z-z'‖) := by
  let χ : ContDiffBump (0 : Position) := ⟨r/4, r/2, by linarith, by linarith⟩
  have hχ0 : (χ : Position → ℝ) =ᶠ[𝓝 (0 : Position)] fun _ => (1 : ℝ) :=
    χ.eventuallyEq_one
  have hQ := contDiff_cutoffHarmonicKernel χ.contDiff hχ0
  have hQc := hasCompactSupport_cutoffHarmonicKernel χ.hasCompactSupport
  obtain ⟨M, hM⟩ := hQc.exists_bound_of_continuous hQ.continuous
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hQc hQ (by simp)
  let C : ℝ := max M L+1
  have hLC : (L : ℝ) ≤ C := by
    dsimp [C]
    linarith [le_max_right M (L : ℝ)]
  have hMC : M ≤ C := by
    dsimp [C]
    linarith [le_max_left M (L : ℝ)]
  have hC : 0 < C := by
    dsimp [C]
    linarith [le_max_right M (L : ℝ), L.coe_nonneg]
  refine ⟨C, hC, ?_⟩
  intro c h hh hharm
  have hs {z : Position} (hz : z ∈ Metric.closedBall c r) :
      ∀ x ∈ tsupport (χ : Position → ℝ), z+x ∈ Metric.ball c (2*r) := by
    intro x hx
    rw [χ.tsupport_eq] at hx
    have hx' : ‖x‖ ≤ r/2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    have hz' : ‖z-c‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    rw [Metric.mem_ball, dist_eq_norm, show z+x-c = (z-c)+x by abel]
    exact lt_of_le_of_lt ((norm_add_le _ _).trans (add_le_add hz' hx')) (by linarith)
  have hsW {z : Position} (hz : z ∈ Metric.closedBall c r) :
      ∀ x ∈ tsupport (χ : Position → ℝ), z+x ∈ Metric.closedBall c (2*r) :=
    fun x hx => Metric.ball_subset_closedBall (hs hz x hx)
  have hI : 0 ≤ ∫ x in Metric.closedBall c (2*r), ‖h x‖ := integral_nonneg (fun _ => norm_nonneg _)
  constructor
  · intro z hz
    exact (harmonic_value_bound hh hharm χ.contDiff χ.hasCompactSupport hχ0.eq_of_nhds
      (isCompact_closedBall c (2*r)) hM (hs hz) (hsW hz)).trans (mul_le_mul_of_nonneg_right hMC hI)
  · intro z hz z' hz'
    exact (harmonic_difference_bound hh hharm χ.contDiff χ.hasCompactSupport hχ0
      (isCompact_closedBall c (2*r)) hL (hs hz) (hs hz') (hsW hz) (hsW hz')).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLC hI) (norm_nonneg _))

theorem HasWeakLaplacian.congrOn {h g q : Position → ℝ} {U : Set Position}
    (hh : HasWeakLaplacian h U q) (he : Set.EqOn h g U) : HasWeakLaplacian g U q := by
  intro φ hφ hφc hφU
  calc
    (∫ x, g x*coordinateLaplacian φ x) = ∫ x, h x*coordinateLaplacian φ x := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      change g x*coordinateLaplacian φ x = h x*coordinateLaplacian φ x
      by_cases hx : x ∈ tsupport φ
      · rw [he (hφU hx)]
      · simp only [coordinateLaplacian_eq_zero_of_notMem_tsupport hx, mul_zero]
    _ = _ := hh φ hφ hφc hφU

theorem harmonic_interior_estimates_local {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : Position) (h : Position → ℝ),
      ContinuousOn h (Metric.ball c (3*r)) →
      HasWeakLaplacian h (Metric.ball c (2*r)) (fun _ => 0) →
      (∀ z ∈ Metric.closedBall c r, ‖h z‖ ≤ C*(∫ x in Metric.closedBall c (2*r), ‖h x‖)) ∧
      (∀ z ∈ Metric.closedBall c r, ∀ z' ∈ Metric.closedBall c r,
        ‖h z-h z'‖ ≤ C*(∫ x in Metric.closedBall c (2*r), ‖h x‖)*‖z-z'‖) := by
  obtain ⟨C, hC, hest⟩ := harmonic_interior_estimates hr
  refine ⟨C, hC, ?_⟩
  intro c h hh hharm
  let η : ContDiffBump c := ⟨2*r, 5*r/2, by positivity, by linarith⟩
  let g : Position → ℝ := fun x => η x*h x
  have hgOn : ContinuousOn g (Metric.ball c (3*r)) := η.continuous.continuousOn.mul hh
  have hg : Continuous g := hgOn.continuous_of_tsupport_subset Metric.isOpen_ball (by
    intro x hx
    have hx' : x ∈ tsupport (η : Position → ℝ) :=
      closure_mono (Function.support_mul_subset_left _ _) hx
    rw [η.tsupport_eq] at hx'
    have hd : dist x c ≤ 5*r/2 := hx'
    exact lt_of_le_of_lt hd (by linarith))
  have he : Set.EqOn g h (Metric.closedBall c (2*r)) := by
    intro x hx
    dsimp [g]
    rw [η.one_of_mem_closedBall hx, one_mul]
  have hgarm : HasWeakLaplacian g (Metric.ball c (2*r)) (fun _ => 0) :=
    hharm.congrOn (fun x hx => (he (Metric.ball_subset_closedBall hx)).symm)
  have hI : (∫ x in Metric.closedBall c (2*r), ‖g x‖) =
      ∫ x in Metric.closedBall c (2*r), ‖h x‖ := by
    apply setIntegral_congr_fun measurableSet_closedBall
    intro x hx
    change ‖g x‖ = ‖h x‖
    rw [he hx]
  have hes {z : Position} (hz : z ∈ Metric.closedBall c r) : g z = h z :=
    he (Metric.closedBall_subset_closedBall (by linarith) hz)
  obtain ⟨hval, hdiff⟩ := hest c g hg hgarm
  constructor
  · intro z hz
    simpa only [hes hz, hI] using hval z hz
  · intro z hz z' hz'
    simpa only [hes hz, hes hz', hI] using hdiff z hz z' hz'

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_HarmonicScale
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
noncomputable section
namespace NeutralAtom

theorem local_harmonic_part {F σ ρ : Position → ℝ} {U : Set Position} {A : ℝ}
    (hU : IsOpen U) (hF : ContinuousOn F U)
    (hpoisson : HasWeakLaplacian F U (fun x => 4*Real.pi*σ x))
    (hρ : Integrable ρ) (hρpos : ∀ x, 0 ≤ ρ x) (hρbd : ∀ x, ρ x ≤ A)
    (he : Set.EqOn σ ρ U) :
    HasWeakLaplacian (fun x => F x+potentialOf ρ x) U (fun _ => 0) := by
  intro φ hφ hφc hφU
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top)
  have hiF : Integrable (fun x => F x*coordinateLaplacian φ x) :=
    integrable_mul_compact_of_continuousAt (fun x hx =>
      hU.continuousOn_iff.mp hF (hφU (tsupport_coordinateLaplacian_subset φ hx)))
      (continuous_coordinateLaplacian hφ2) (hasCompactSupport_coordinateLaplacian hφc)
  have hiP : Integrable (fun x => potentialOf ρ x*coordinateLaplacian φ x) :=
    ((potentialOf_continuous hρ hρpos hρbd).mul (continuous_coordinateLaplacian hφ2)).integrable_of_hasCompactSupport
      (hasCompactSupport_coordinateLaplacian hφc).mul_left
  have heq : (fun x => (F x+potentialOf ρ x)*coordinateLaplacian φ x) =
      fun x => F x*coordinateLaplacian φ x+potentialOf ρ x*coordinateLaplacian φ x := by
    ext x
    ring
  have hrho : (fun x => -(4*Real.pi)*ρ x*φ x) = fun x => -(4*Real.pi*σ x*φ x) := by
    ext x
    by_cases hx : x ∈ tsupport φ
    · rw [he (hφU hx)]
      ring
    · simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero, neg_zero]
  rw [heq, integral_add hiF hiP, hpoisson φ hφ hφc hφU,
    potentialOf_weakLaplacian hρ φ hφ hφc (Set.subset_univ _), hrho, integral_neg]
  simp only [add_neg_cancel, zero_mul, integral_zero]

theorem HasWeakLaplacian.dilate {F q : Position → ℝ} {U : Set Position}
    {D : ℝ} (hD : 0 < D) (hw : HasWeakLaplacian F U q) :
    HasWeakLaplacian (fun x => D^4*F (D • x)) ((fun x => D • x) ⁻¹' U)
      (fun x => D^6*q (D • x)) := by
  intro φ hφ hc ht
  let e : Position ≃ₜ Position := Homeomorph.smul (Units.mk0 D⁻¹ (inv_ne_zero hD.ne'))
  let ψ : Position → ℝ := fun x => φ (D⁻¹ • x)
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp (contDiff_id.const_smul D⁻¹)
  have hψc : HasCompactSupport ψ := hc.comp_homeomorph e
  have hψt : tsupport ψ ⊆ U := by
    intro x hx
    have hx' : e x ∈ tsupport φ := by
      simpa only [ψ, show (fun x : Position => D⁻¹ • x) = e from rfl,
        ← Function.comp_def, tsupport_comp_eq_preimage, Set.mem_preimage] using hx
    have := ht hx'
    simpa only [Set.mem_preimage, e, Homeomorph.smul_apply, Units.smul_def,
      Units.val_mk0, smul_smul, mul_inv_cancel₀ hD.ne', one_smul] using this
  have hid (x : Position) : D⁻¹ • (D • x) = x := by
    rw [smul_smul, inv_mul_cancel₀ hD.ne', one_smul]
  have hLap (x : Position) : coordinateLaplacian ψ (D • x) =
      (D⁻¹)^2*coordinateLaplacian φ x := by
    change coordinateLaplacian (fun y => φ (D⁻¹ • y)) (D • x) = _
    rw [coordinateLaplacian_comp_smul, hid]
  have hleft := Measure.integral_comp_smul_of_nonneg volume
    (fun x => F x*coordinateLaplacian ψ x) D (hR := hD.le)
  have hright := Measure.integral_comp_smul_of_nonneg volume
    (fun x => q x*ψ x) D (hR := hD.le)
  simp only [Position, finrank_euclideanSpace_fin, smul_eq_mul] at hleft hright
  simp_rw [hLap, show ∀ x, F (D • x)*((D⁻¹)^2*coordinateLaplacian φ x) =
    (D⁻¹)^2*(F (D • x)*coordinateLaplacian φ x) by intro x; ring,
    integral_const_mul] at hleft
  simp only [ψ, hid] at hright
  have hwe := hw ψ hψ hψc hψt
  have hEq : (∫ x, F (D • x)*coordinateLaplacian φ x) = D^2*(∫ x, q (D • x)*φ x) := by
    rw [hwe, ← hright] at hleft
    field_simp [hD.ne'] at hleft
    nlinarith [hleft]
  simp_rw [mul_assoc, integral_const_mul]
  rw [hEq]
  ring

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_PoissonInterior
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Filter Set
open scoped Topology BigOperators ContDiff
namespace NeutralAtom
theorem poisson_interior_estimates (c : Position) {r A M : ℝ}
    (hr : 0 < r) (hA : 0 ≤ A) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F σ : Position → ℝ),
      ContinuousOn F (Metric.ball c (3*r)) →
      HasWeakLaplacian F (Metric.ball c (2*r)) (fun x => 4*Real.pi*σ x) →
      Integrable σ → (∀ x, 0 ≤ σ x) →
      (∀ x ∈ Metric.closedBall c (3*r), σ x ≤ A) →
      (∫ x in Metric.closedBall c (2*r), ‖F x‖) ≤ M →
      (∀ z ∈ Metric.closedBall c r, ‖F z‖ ≤ C) ∧
      (∀ z ∈ Metric.closedBall c r, ∀ z' ∈ Metric.closedBall c r,
        ‖F z-F z'‖ ≤ C*‖z-z'‖) := by
  obtain ⟨HC, hHC, hest⟩ := harmonic_interior_estimates_local hr
  let W := Metric.closedBall c (3*r)
  let W' := Metric.closedBall c (2*r)
  let V := (volume W).toReal
  let V' := (volume W').toReal
  let PB := A*(∫ y in Metric.ball (0 : Position) 1, coulombKernel y)+A*V
  let LB := A*(∫ y in Metric.ball (0 : Position) 1, (coulombKernel y)^2)+A*V
  have hPB : 0 ≤ PB := add_nonneg (mul_nonneg hA (integral_nonneg coulombKernel_nonneg))
    (mul_nonneg hA ENNReal.toReal_nonneg)
  have hLB : 0 ≤ LB := add_nonneg (mul_nonneg hA (integral_nonneg (fun y => sq_nonneg _)))
    (mul_nonneg hA ENNReal.toReal_nonneg)
  let H := M+PB*V'
  have hH : 0 ≤ H := add_nonneg hM (mul_nonneg hPB ENNReal.toReal_nonneg)
  let C := HC*H+PB+LB+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro F σ hF hpoisson hσ hσpos hσbd hIF
  let ρ := W.indicator σ
  have hρ : Integrable ρ := hσ.indicator measurableSet_closedBall
  have hρpos : ∀ x, 0 ≤ ρ x := fun x => Set.indicator_nonneg (fun y _ => hσpos y) x
  have hρbd : ∀ x, ρ x ≤ A := by
    intro x
    by_cases hx : x ∈ W
    · simpa only [ρ, Set.indicator_of_mem hx] using hσbd x hx
    · simpa only [ρ, Set.indicator_of_notMem hx] using hA
  have hmass : (∫ x, ρ x) ≤ A*V := by
    rw [show ρ = W.indicator σ from rfl, integral_indicator measurableSet_closedBall]
    calc
      (∫ x in W, σ x) ≤ ∫ _ in W, A := integral_mono_ae hσ.integrableOn
        (integrableOn_const (isCompact_closedBall c (3*r)).measure_ne_top)
        ((ae_restrict_mem measurableSet_closedBall).mono (fun x hx => hσbd x hx))
      _ = A*V := by simp only [integral_const, Measure.restrict_apply_univ, smul_eq_mul, V,
          measureReal_def, mul_comm]
  let P := potentialOf ρ
  have hPcont : Continuous P := potentialOf_continuous hρ hρpos hρbd
  have hPbd (x : Position) : ‖P x‖ ≤ PB := by
    have hp : 0 ≤ P x := integral_nonneg (fun y => mul_nonneg (coulombKernel_nonneg _) (hρpos y))
    rw [Real.norm_eq_abs, abs_of_nonneg hp]
    exact (bounded_density_convolution measurable_coulombKernel coulombKernel_nonneg
      (coulombKernel_integrableOn_ball 1) (fun _ => coulombKernel_le_one)
      hρ hρpos hρbd x).2.trans (by dsimp only [PB]; linarith)
  have hPlip (x y : Position) : ‖P x-P y‖ ≤ LB*‖x-y‖ :=
    (potentialOf_lipschitz_bound hρ hρpos hρbd x y).trans
      (mul_le_mul_of_nonneg_right (by dsimp only [LB]; linarith) (norm_nonneg _))
  have hW' : W' ⊆ Metric.ball c (3*r) := by
    intro x hx
    change dist x c ≤ 2*r at hx
    change dist x c < 3*r
    linarith
  have hball : Metric.ball c (2*r) ⊆ Metric.ball c (3*r) :=
    Metric.ball_subset_ball (by linarith)
  let h : Position → ℝ := fun x => F x+P x
  have hhcont : ContinuousOn h (Metric.ball c (3*r)) := hF.add hPcont.continuousOn
  have hharm : HasWeakLaplacian h (Metric.ball c (2*r)) (fun _ => 0) :=
    local_harmonic_part Metric.isOpen_ball (hF.mono hball) hpoisson hρ hρpos hρbd (by
      intro x hx
      have hxW : x ∈ W := by
        change dist x c ≤ 3*r
        exact (hball hx).le
      exact (Set.indicator_of_mem hxW σ).symm)
  have hiF : IntegrableOn (fun x => ‖F x‖) W' :=
    ((hF.mono hW').norm).integrableOn_compact (isCompact_closedBall c (2*r))
  have hih : IntegrableOn (fun x => ‖h x‖) W' :=
    ((hhcont.mono hW').norm).integrableOn_compact (isCompact_closedBall c (2*r))
  have hiPB : IntegrableOn (fun _ : Position => PB) W' :=
    integrableOn_const (isCompact_closedBall c (2*r)).measure_ne_top
  have hIh : (∫ x in W', ‖h x‖) ≤ H := by
    calc
      (∫ x in W', ‖h x‖) ≤ ∫ x in W', ‖F x‖+PB := integral_mono_ae hih (hiF.add hiPB)
        (Filter.Eventually.of_forall (fun x => (norm_add_le (F x) (P x)).trans
          (add_le_add le_rfl (hPbd x))))
      _ = (∫ x in W', ‖F x‖)+PB*V' := by
        rw [integral_add hiF hiPB, integral_const]
        simp only [Measure.restrict_apply_univ, smul_eq_mul, V', measureReal_def, mul_comm]
      _ ≤ H := by dsimp only [H]; linarith
  obtain ⟨hval, hdiff⟩ := hest c h hhcont hharm
  have hCval : HC*H+PB ≤ C := by dsimp [C]; linarith
  have hClip : HC*H+LB ≤ C := by dsimp [C]; linarith
  constructor
  · intro z hz
    calc
      ‖F z‖ = ‖h z-P z‖ := by dsimp [h]; rw [add_sub_cancel_right]
      _ ≤ ‖h z‖+‖P z‖ := norm_sub_le _ _
      _ ≤ HC*(∫ x in W', ‖h x‖)+PB := add_le_add (hval z hz) (hPbd z)
      _ ≤ HC*H+PB := by linarith [mul_le_mul_of_nonneg_left hIh hHC.le]
      _ ≤ C := hCval
  · intro z hz z' hz'
    calc
      ‖F z-F z'‖ = ‖(h z-h z')-(P z-P z')‖ := by congr 1; dsimp [h]; ring
      _ ≤ ‖h z-h z'‖+‖P z-P z'‖ := norm_sub_le _ _
      _ ≤ HC*(∫ x in W', ‖h x‖)*‖z-z'‖+LB*‖z-z'‖ :=
        add_le_add (hdiff z hz z' hz') (hPlip z z')
      _ ≤ (HC*H+LB)*‖z-z'‖ := by
        have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hIh hHC.le)
          (norm_nonneg (z-z'))
        nlinarith
      _ ≤ C*‖z-z'‖ := mul_le_mul_of_nonneg_right hClip (norm_nonneg _)

end NeutralAtom

end
open MeasureTheory Filter Set
open scoped Topology BigOperators ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RadialBounds_Radial
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open ContinuousLinearMap
open scoped Topology BigOperators ContDiff Convolution Pointwise ENNReal
namespace NeutralAtom

theorem potentialOf_isometry {w : Position → ℝ} (hw : IsRadial w)
    (T : Position ≃ₗᵢ[ℝ] Position) (x : Position) :
    potentialOf w (T x) = potentialOf w x := by
  unfold potentialOf
  rw [← T.measurePreserving.integral_comp T.toMeasurableEquiv.measurableEmbedding]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [← T.map_sub]
  simp only [coulombKernel, T.norm_map]
  rw [hw (T y) y (T.norm_map y)]

theorem potentialOf_radial {w : Position → ℝ} (hw : IsRadial w) :
    IsRadial (potentialOf w) := by
  intro x y hxy
  let T : Position ≃ₗᵢ[ℝ] Position := (ℝ ∙ (x-y))ᗮ.reflection
  have hT : T x = y := Submodule.reflection_sub hxy
  rw [← hT]
  exact (potentialOf_isometry hw T x).symm

theorem radial_potential_le_center {w : Position → ℝ} {A : ℝ}
    (hi : Integrable w) (hp : ∀ x, 0 ≤ w x) (hb : ∀ x, w x ≤ A)
    (hr : IsRadial w) (x : Position) : potentialOf w x ≤ potentialOf w 0 := by
  by_cases hx : x = 0
  · simp [hx]
  have hR : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hcont := potentialOf_continuous hi hp hb
  have hrad := potentialOf_radial hr
  have hw : WeakLaplacianLower (fun y => potentialOf w x-potentialOf w y)
      (Metric.ball 0 ‖x‖ ∩ {y | 0 < potentialOf w x-potentialOf w y}) 0 := by
    intro φ hφ hc _ hpos
    have hL : Continuous (coordinateLaplacian φ) :=
      continuous_coordinateLaplacian (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top))
    have hLc := hasCompactSupport_coordinateLaplacian hc
    have hiP : Integrable (fun y => potentialOf w y*coordinateLaplacian φ y) :=
      integrable_mul_compact_of_continuousAt (fun _ _ => hcont.continuousAt) hL hLc
    simp_rw [sub_mul]
    rw [integral_sub ((hL.integrable_of_hasCompactSupport hLc).const_mul _) hiP,
      integral_const_mul, integral_coordinateLaplacian hφ hc,
      potentialOf_weakLaplacian hi φ hφ hc (Set.subset_univ _)]
    simp only [zero_mul, mul_zero, zero_sub, neg_mul, integral_neg, neg_neg]
    exact integral_nonneg (fun y => mul_nonneg (mul_nonneg (by positivity) (hp y)) (hpos y))
  have hh := weak_maximum_principle_closedBall hR
    (continuous_const.sub hcont).continuousOn
    (fun y hy => by
      change potentialOf w x-potentialOf w y ≤ 0
      rw [hrad y x hy, sub_self]) hw
    (0 : Position) (by simp [hR.le])
  change potentialOf w x-potentialOf w 0 ≤ 0 at hh
  linarith

theorem integrable_coulomb_pairing {ρ w : Position → ℝ} {C : ℝ}
    (hρ : Integrable ρ) (hw : Integrable w) (hb : ∀ x, ‖w x‖ ≤ C) :
    Integrable (fun z : Position × Position => coulombKernel (z.1-z.2)*ρ z.2*w z.1)
      (volume.prod volume) := by
  let k : Position → ℝ := (Metric.ball 0 1).indicator coulombKernel
  have hk : Integrable k :=
    (coulombKernel_integrableOn_ball 1).integrable_indicator measurableSet_ball
  have hn : Integrable (fun z : Position × Position => ‖ρ z.2‖*k (z.1-z.2))
      (volume.prod volume) := by
    simpa using hρ.norm.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hk
  have hf : Integrable (fun z : Position × Position => ‖w z.1‖*‖ρ z.2‖)
      (volume.prod volume) := hw.norm.mul_prod hρ.norm
  have hm : AEStronglyMeasurable
      (fun z : Position × Position => coulombKernel (z.1-z.2)*ρ z.2*w z.1)
      (volume.prod volume) := by
    have hh := hρ.aestronglyMeasurable.convolution_integrand
      (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) measurable_coulombKernel.aestronglyMeasurable
    have hh' : AEStronglyMeasurable
        (fun z : Position × Position => ρ z.2*coulombKernel (z.1-z.2)*w z.1)
        (volume.prod volume) := hh.mul hw.aestronglyMeasurable.comp_fst
    convert hh' using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    ring
  refine Integrable.mono' ((hn.const_mul C).add hf) hm (Filter.Eventually.of_forall ?_)
  intro z
  have hK : coulombKernel (z.1-z.2) ≤ k (z.1-z.2)+1 := by
    by_cases hz : z.1-z.2 ∈ Metric.ball (0 : Position) 1
    · simp only [k, Set.indicator_of_mem hz]
      linarith
    · have hl : 1 ≤ ‖z.1-z.2‖ := by simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hz
      have hh : ‖z.1-z.2‖⁻¹ ≤ (1:ℝ) := by simpa using inv_anti₀ (by norm_num : (0:ℝ)<1) hl
      simpa only [k, Set.indicator_of_notMem hz, zero_add, coulombKernel] using hh
  have hkpos : 0 ≤ k (z.1-z.2) := Set.indicator_nonneg (fun y _ => coulombKernel_nonneg y) _
  rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg (coulombKernel_nonneg _)]
  calc
    coulombKernel (z.1-z.2)*‖ρ z.2‖*‖w z.1‖ ≤
        (k (z.1-z.2)+1)*‖ρ z.2‖*‖w z.1‖ := by gcongr
    _ = ‖ρ z.2‖*k (z.1-z.2)*‖w z.1‖+‖w z.1‖*‖ρ z.2‖ := by ring
    _ ≤ C*(‖ρ z.2‖*k (z.1-z.2))+‖w z.1‖*‖ρ z.2‖ := by
      nlinarith [mul_nonneg (norm_nonneg (ρ z.2)) hkpos,
        mul_le_mul_of_nonneg_left (hb z.1) (mul_nonneg (norm_nonneg (ρ z.2)) hkpos)]

theorem coulomb_pairing_comm {ρ w : Position → ℝ} {C : ℝ}
    (hρ : Integrable ρ) (hw : Integrable w) (hb : ∀ x, ‖w x‖ ≤ C) :
    (∫ x, potentialOf ρ x*w x) = ∫ y, potentialOf w y*ρ y := by
  calc
    (∫ x, potentialOf ρ x*w x) = ∫ x, ∫ y, coulombKernel (x-y)*ρ y*w x := by
      simp only [potentialOf, integral_mul_const]
    _ = ∫ y, ∫ x, coulombKernel (x-y)*ρ y*w x :=
      integral_integral_swap (integrable_coulomb_pairing hρ hw hb)
    _ = ∫ y, potentialOf w y*ρ y := by
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [potentialOf, ← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [coulombKernel, norm_sub_rev x y]
      ring

theorem neutral_radial_average_nonneg {σ w : Position → ℝ} {lam Aσ Aw : ℝ}
    (hσ : Integrable σ) (hσpos : ∀ x, 0 ≤ σ x) (hσbd : ∀ x, σ x ≤ Aσ)
    (hmass : (∫ x, σ x) = lam)
    (hw : Integrable w) (hwpos : ∀ x, 0 ≤ w x) (hwbd : ∀ x, w x ≤ Aw)
    (hwrad : IsRadial w) :
    0 ≤ ∫ x, (lam*coulombKernel x-potentialOf σ x)*w x := by
  have hwabs : ∀ x, ‖w x‖ ≤ Aw := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hwpos x)]
    exact hwbd x
  have hiK : Integrable (fun x => coulombKernel x*w x) := by
    have hh := (bounded_density_convolution measurable_coulombKernel coulombKernel_nonneg
      (coulombKernel_integrableOn_ball 1) (fun _ h => coulombKernel_le_one h)
      hw hwpos hwbd (0 : Position)).1
    simpa [coulombKernel] using hh
  have hiP : Integrable (fun x => potentialOf σ x*w x) := by
    have hh := (integrable_coulomb_pairing hσ hw hwabs).integral_prod_left
    simpa only [potentialOf, integral_mul_const] using hh
  have hiPw : Integrable (fun x => potentialOf w x*σ x) := by
    have hh := (integrable_coulomb_pairing hw hσ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hσpos x)]
      exact hσbd x)).integral_prod_left
    simpa only [potentialOf, integral_mul_const] using hh
  have hmax : ∀ x, potentialOf w x*σ x ≤ potentialOf w 0*σ x := fun x =>
    mul_le_mul_of_nonneg_right (radial_potential_le_center hw hwpos hwbd hwrad x) (hσpos x)
  have hle := integral_mono hiPw (hσ.const_mul (potentialOf w 0)) hmax
  rw [integral_const_mul, hmass] at hle
  have hzero : potentialOf w 0 = ∫ x, coulombKernel x*w x := by
    simp only [potentialOf, coulombKernel, zero_sub, norm_neg]
  simp_rw [sub_mul]
  have hilam : Integrable (fun x => lam*coulombKernel x*w x) := by
    simpa only [mul_assoc] using hiK.const_mul lam
  rw [integral_sub hilam hiP, coulomb_pairing_comm hσ hw hwabs]
  simp_rw [mul_assoc lam, integral_const_mul]
  rw [← hzero]
  nlinarith

theorem neutral_weighted_lone_bound {σ w : Position → ℝ} {lam Aσ Aw B : ℝ}
    (hσ : Integrable σ) (hσpos : ∀ x, 0 ≤ σ x) (hσbd : ∀ x, σ x ≤ Aσ)
    (hmass : (∫ x, σ x) = lam)
    (hw : Integrable w) (hwpos : ∀ x, 0 ≤ w x) (hwbd : ∀ x, w x ≤ Aw)
    (hwrad : IsRadial w) (hB : 0 ≤ B)
    (hcap : ∀ x, w x ≠ 0 → lam*coulombKernel x-potentialOf σ x ≤ B) :
    (∫ x, |lam*coulombKernel x-potentialOf σ x| *w x) ≤ 2*B*(∫ x, w x) := by
  let F (x : Position) := lam*coulombKernel x-potentialOf σ x
  have hwabs : ∀ x, ‖w x‖ ≤ Aw := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hwpos x)]
    exact hwbd x
  have hiK : Integrable (fun x => coulombKernel x*w x) := by
    have hh := (bounded_density_convolution measurable_coulombKernel coulombKernel_nonneg
      (coulombKernel_integrableOn_ball 1) (fun _ h => coulombKernel_le_one h)
      hw hwpos hwbd (0 : Position)).1
    simpa [coulombKernel] using hh
  have hiP : Integrable (fun x => potentialOf σ x*w x) := by
    have hh := (integrable_coulomb_pairing hσ hw hwabs).integral_prod_left
    simpa only [potentialOf, integral_mul_const] using hh
  have hiF : Integrable (fun x => F x*w x) := by
    simpa only [Pi.sub_def, F, sub_mul, mul_assoc] using (hiK.const_mul lam).sub hiP
  have hiabs : Integrable (fun x => |F x| *w x) := by
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hwpos _)] using hiF.norm
  have hle : ∀ x, |F x| *w x ≤ 2*B*w x-F x*w x := by
    intro x
    by_cases hx : w x = 0
    · simp [hx]
    · have hh := hcap x hx
      have hh' : |F x| ≤ 2*B-F x := by
        rw [abs_le]
        constructor <;> dsimp [F] <;> linarith
      nlinarith [mul_le_mul_of_nonneg_right hh' (hwpos x)]
  have hh := integral_mono hiabs ((hw.const_mul (2*B)).sub hiF) hle
  simp only [Pi.sub_apply] at hh
  rw [integral_sub (hw.const_mul (2*B)) hiF, integral_const_mul] at hh
  have hmean := neutral_radial_average_nonneg hσ hσpos hσbd hmass hw hwpos hwbd hwrad
  change 0 ≤ ∫ x, F x*w x at hmean
  linarith

theorem neutral_annulus_lone_bound {σ : Position → ℝ} {lam Aσ C a b : ℝ}
    (hσ : Integrable σ) (hσpos : ∀ x, 0 ≤ σ x) (hσbd : ∀ x, σ x ≤ Aσ)
    (hmass : (∫ x, σ x) = lam) (ha : 0 < a) (hC : 0 ≤ C)
    (hcap : ∀ x : Position, a ≤ ‖x‖ → ‖x‖ ≤ b →
      lam*coulombKernel x-potentialOf σ x ≤ C/(‖x‖^4)) :
    (∫ x in {x : Position | a ≤ ‖x‖ ∧ ‖x‖ ≤ b},
      |lam*coulombKernel x-potentialOf σ x|) ≤
    2*(C/a^4)*(volume {x : Position | a ≤ ‖x‖ ∧ ‖x‖ ≤ b}).toReal := by
  let s : Set Position := {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ b}
  let w : Position → ℝ := s.indicator (fun _ => 1)
  have hs : IsCompact s := by
    have hs' : s = Metric.closedBall (0 : Position) b ∩ {x | a ≤ ‖x‖} := by
      ext x
      simp only [s, Set.mem_ofPred_eq, Set.mem_inter_iff, Metric.mem_closedBall,
        dist_zero_right, and_comm]
    rw [hs']
    exact (isCompact_closedBall (0 : Position) b).inter_right (isClosed_le continuous_const continuous_norm)
  have hw : Integrable w := by
    apply (integrable_indicator_iff hs.measurableSet).mpr
    exact integrableOn_const hs.measure_ne_top
  have hwpos : ∀ x, 0 ≤ w x := fun x => Set.indicator_nonneg (fun _ _ => by norm_num) x
  have hwbd : ∀ x, w x ≤ 1 := by
    intro x
    by_cases hx : x ∈ s <;> simp [w, hx]
  have hwrad : IsRadial w := by
    intro x y hxy
    by_cases hx : a ≤ ‖x‖ ∧ ‖x‖ ≤ b
    · have hy : a ≤ ‖y‖ ∧ ‖y‖ ≤ b := by simpa only [hxy] using hx
      simp [w, s, hx, hy]
    · have hy : ¬(a ≤ ‖y‖ ∧ ‖y‖ ≤ b) := by simpa only [hxy] using hx
      simp [w, s, hx, hy]
  have hB : 0 ≤ C/a^4 := div_nonneg hC (by positivity)
  have hcap' : ∀ x, w x ≠ 0 → lam*coulombKernel x-potentialOf σ x ≤ C/a^4 := by
    intro x hx
    have hxs : x ∈ s := by
      by_contra h
      exact hx (Set.indicator_of_notMem h _)
    exact (hcap x hxs.1 hxs.2).trans
      (div_le_div_of_nonneg_left hC (by positivity) (pow_le_pow_left₀ ha.le hxs.1 4))
  have hh := neutral_weighted_lone_bound hσ hσpos hσbd hmass hw hwpos hwbd hwrad hB hcap'
  have heq : (fun x => |lam*coulombKernel x-potentialOf σ x| *w x) =
      s.indicator (fun x => |lam*coulombKernel x-potentialOf σ x|) := by
    ext x
    by_cases hx : x ∈ s <;> simp [w, hx]
  rw [heq, integral_indicator hs.measurableSet] at hh
  have hiw : (∫ x, w x) = (volume s).toReal := by
    rw [show w = s.indicator (fun _ => (1:ℝ)) from rfl,
      integral_indicator hs.measurableSet, integral_const]
    simp only [Measure.restrict_apply_univ, smul_eq_mul, mul_one, measureReal_def]
  rw [hiw] at hh
  exact hh

theorem locallyUniform_subsequence_of_equicontinuous
    {X : Type*} [PseudoMetricSpace X] [LocallyCompactSpace X]
    [SecondCountableTopology X]
    (F : ℕ → C(X, ℝ))
    (heq : Equicontinuous (fun n x => F n x))
    (hbd : ∀ x, ∃ M : ℝ, ∀ n, ‖F n x‖ ≤ M) :
    ∃ f : C(X, ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoLocallyUniformly (fun n x => F (φ n) x) f atTop := by
  let : T2Space (UniformOnFun X ℝ {K : Set X | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (by
      apply Set.eq_univ_of_forall
      intro x
      exact Set.mem_sUnion_of_mem (Set.mem_singleton x) isCompact_singleton)
  let S := Set.range F
  have hs : IsCompact (closure S) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := fun f : C(X, ℝ) => (f : X → ℝ))
      (𝔖 := {K : Set X | IsCompact K}) (fun _ hK => hK)
      ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
    · intro K _
      let pick : S → ℕ := fun f => Classical.choose f.property
      have hp (f : S) : F (pick f) = f.val := Classical.choose_spec f.property
      have hh := (heq.comp pick).equicontinuousOn K
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      ext f x
      exact congrArg (fun u : C(X, ℝ) => u x) (hp f).symm
    · intro K _ x _
      obtain ⟨M, hM⟩ := hbd x
      refine ⟨Set.Icc (-M) M, isCompact_Icc, ?_⟩
      rintro f ⟨n, rfl⟩
      exact abs_le.mp (hM n)
  obtain ⟨f, _, φ, hφ, ht⟩ := hs.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  refine ⟨f, φ, hφ, ?_⟩
  exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp ht

theorem equicontinuous_of_eventual_local_lipschitz
    {X : Type*} [PseudoMetricSpace X] (F : ℕ → X → ℝ)
    (hc : ∀ n, Continuous (F n))
    (hl : ∀ x, ∃ (r C : ℝ) (N : ℕ), 0 < r ∧ 0 ≤ C ∧
      ∀ n, N ≤ n → ∀ y ∈ Metric.ball x r, ‖F n x-F n y‖ ≤ C*dist y x) :
    Equicontinuous F := by
  intro x
  obtain ⟨r, C, N, hr, hC, hN⟩ := hl x
  apply Metric.equicontinuousAt_iff.mpr
  intro ε hε
  have hf : EquicontinuousAt (fun n : Fin N => F n) x :=
    equicontinuousAt_finite.mpr (fun n => (hc n).continuousAt)
  obtain ⟨δ, hδ, hd⟩ := Metric.equicontinuousAt_iff.mp hf ε hε
  refine ⟨min r (min δ (ε/(C+1))), lt_min hr (lt_min hδ (div_pos hε (by linarith))), ?_⟩
  intro y hy n
  have hyr : dist y x < r := lt_of_lt_of_le hy (min_le_left _ _)
  have hyδ : dist y x < δ := lt_of_lt_of_le hy ((min_le_right _ _).trans (min_le_left _ _))
  have hyε : dist y x < ε/(C+1) :=
    lt_of_lt_of_le hy ((min_le_right _ _).trans (min_le_right _ _))
  by_cases hn : n < N
  · exact hd y hyδ ⟨n, hn⟩
  · have hh := hN n (le_of_not_gt hn) y hyr
    rw [dist_eq_norm]
    have hmul := (lt_div_iff₀ (by linarith : 0 < C+1)).mp hyε
    nlinarith [dist_nonneg (x := y) (y := x)]

theorem norm_bounded_of_eventually_bounded (a : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᶠ n in atTop, ‖a n‖ ≤ C) : ∃ M : ℝ, ∀ n, ‖a n‖ ≤ M := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  refine ⟨C+∑ j ∈ Finset.range N, ‖a j‖, ?_⟩
  intro n
  have hs : 0 ≤ ∑ j ∈ Finset.range N, ‖a j‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  by_cases hn : n < N
  · have hh := Finset.single_le_sum (fun j (_ : j ∈ Finset.range N) => norm_nonneg (a j))
      (Finset.mem_range.mpr hn)
    linarith
  · have hh := hN n (le_of_not_gt hn)
    linarith

theorem locallyUniform_subsequence_of_eventual_ball_estimates
    {X : Type*} [PseudoMetricSpace X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (F : ℕ → X → ℝ)
    (hc : ∀ n, Continuous (F n))
    (he : ∀ x, ∃ (r C : ℝ) (N : ℕ), 0 < r ∧ 0 ≤ C ∧
      ∀ n, N ≤ n → ‖F n x‖ ≤ C ∧
        ∀ y ∈ Metric.ball x r, ∀ z ∈ Metric.ball x r,
          ‖F n y-F n z‖ ≤ C*dist y z) :
    ∃ f : C(X, ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoLocallyUniformly (fun n x => F (φ n) x) f atTop ∧
      LocallyLipschitzOn Set.univ f := by
  let G : ℕ → C(X, ℝ) := fun n => ⟨F n, hc n⟩
  have hEq : Equicontinuous (fun n x => G n x) := by
    apply equicontinuous_of_eventual_local_lipschitz F hc
    intro x
    obtain ⟨r, C, N, hr, hC, hN⟩ := he x
    refine ⟨r, C, N, hr, hC, ?_⟩
    intro n hn y hy
    simpa only [dist_comm x y] using (hN n hn).2 x (Metric.mem_ball_self hr) y hy
  have hBd : ∀ x, ∃ M : ℝ, ∀ n, ‖G n x‖ ≤ M := by
    intro x
    obtain ⟨r, C, N, _, hC, hN⟩ := he x
    exact norm_bounded_of_eventually_bounded (fun n => F n x) hC
      (eventually_atTop.mpr ⟨N, fun n hn => (hN n hn).1⟩)
  obtain ⟨f, φ, hφ, hu⟩ := locallyUniform_subsequence_of_equicontinuous G hEq hBd
  refine ⟨f, φ, hφ, hu, ?_⟩
  intro x _
  obtain ⟨r, C, N, hr, _, hN⟩ := he x
  refine ⟨C.toNNReal, Metric.ball x r, ?_, ?_⟩
  · simpa only [nhdsWithin_univ] using Metric.ball_mem_nhds x hr
  · apply LipschitzOnWith.of_dist_le'
    intro y hy z hz
    have ht (w : X) : Tendsto (fun n => F (φ n) w) atTop (𝓝 (f w)) :=
      hu.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ w)
    have hn : ∀ᶠ n : ℕ in atTop, N ≤ φ n := hφ.tendsto_atTop.eventually (eventually_ge_atTop N)
    have hl := le_of_tendsto ((ht y).sub (ht z)).norm (hn.mono (fun n hn => (hN (φ n) hn).2 y hy z hz))
    simpa only [dist_eq_norm] using hl

theorem screenedField_continuousOn {lam A : ℝ} {σ : Position → ℝ}
    (hi : Integrable σ) (hp : ∀ x, 0 ≤ σ x) (hb : ∀ x, σ x ≤ A) :
    ContinuousOn (screenedField lam σ) {x | x ≠ 0} := by
  intro x hx
  have hk : ContinuousAt coulombKernel x :=
    continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hx)
  exact ((continuousAt_const.mul hk).sub
    (potentialOf_continuous hi hp hb).continuousAt).continuousWithinAt

theorem screenedField_weakLaplacian {lam A : ℝ} {σ : Position → ℝ}
    (hi : Integrable σ) (hp : ∀ x, 0 ≤ σ x) (hb : ∀ x, σ x ≤ A) :
    HasWeakLaplacian (screenedField lam σ) {x | x ≠ 0} (fun x => 4*Real.pi*σ x) := by
  intro φ hφ hc ht
  have hLc : Continuous (coordinateLaplacian φ) :=
    continuous_coordinateLaplacian (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top))
  have hLs := hasCompactSupport_coordinateLaplacian hc
  have hiK : Integrable (fun x => coulombKernel x*coordinateLaplacian φ x) := by
    simpa only [smul_eq_mul, Pi.mul_apply] using
      locallyIntegrable_coulombKernel.integrable_smul_right_of_hasCompactSupport hLc hLs
  have hiP : Integrable (fun x => potentialOf σ x*coordinateLaplacian φ x) :=
    integrable_mul_compact_of_continuousAt (fun _ _ => (potentialOf_continuous hi hp hb).continuousAt)
      hLc hLs
  have hzero : φ 0 = 0 := image_eq_zero_of_notMem_tsupport (fun hx => ht hx rfl)
  calc
    (∫ x, screenedField lam σ x*coordinateLaplacian φ x) =
        lam*(∫ x, coulombKernel x*coordinateLaplacian φ x)-
        ∫ x, potentialOf σ x*coordinateLaplacian φ x := by
      simp only [screenedField, sub_mul, mul_assoc]
      rw [integral_sub (hiK.const_mul lam) hiP, integral_const_mul]
    _ = ∫ x, (4*Real.pi*σ x)*φ x := by
      rw [integral_coulombKernel_laplacian hφ hc, hzero,
        potentialOf_weakLaplacian hi φ hφ hc (Set.subset_univ _)]
      simp only [mul_zero, neg_zero, zero_sub, ← integral_neg]
      congr 1
      ext x
      ring

theorem isCompact_closedNormAnnulus (a b : ℝ) :
    IsCompact {x : Position | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} := by
  have he : {x : Position | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} =
      Metric.closedBall (0 : Position) b ∩ {x | a ≤ ‖x‖} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Metric.mem_closedBall,
      dist_zero_right, and_comm]
  rw [he]
  exact (isCompact_closedBall (0 : Position) b).inter_right (isClosed_le continuous_const continuous_norm)

end NeutralAtom
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_PuncturedPosition
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open ContinuousLinearMap
open scoped Topology BigOperators ContDiff Convolution Pointwise ENNReal
namespace NeutralAtom

theorem closedBall_eighth_subset_annulus {c : Position} (hc : c ≠ 0) :
    Metric.closedBall c (3*(‖c‖/8)) ⊆ {x : Position | ‖c‖/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 2*‖c‖} := by
  intro x hx
  change dist x c ≤ 3*(‖c‖/8) at hx
  rw [dist_eq_norm] at hx
  have hn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have h1 := norm_sub_norm_le x c
  have h2 := norm_sub_norm_le c x
  rw [norm_sub_rev] at h2
  constructor <;> linarith

theorem neutral_screened_ball_estimates {c : Position} (hc : c ≠ 0) {C A : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) :
    ∃ D : ℝ, 0 < D ∧ ∀ (lam Aσ : ℝ) (σ : Position → ℝ),
      Integrable σ → (∀ x, 0 ≤ σ x) → (∀ x, σ x ≤ Aσ) → (∫ x, σ x) = lam →
      (∀ x : Position, ‖c‖/2 ≤ ‖x‖ → ‖x‖ ≤ 2*‖c‖ →
        screenedField lam σ x ≤ C/‖x‖^4 ∧ σ x ≤ A) →
      (∀ z ∈ Metric.closedBall c (‖c‖/8), ‖screenedField lam σ z‖ ≤ D) ∧
      (∀ z ∈ Metric.closedBall c (‖c‖/8), ∀ z' ∈ Metric.closedBall c (‖c‖/8),
        ‖screenedField lam σ z-screenedField lam σ z'‖ ≤ D*‖z-z'‖) := by
  let r := ‖c‖/8
  let V := {x : Position | ‖c‖/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 2*‖c‖}
  let M := 2*(C/(‖c‖/2)^4)*(volume V).toReal
  have hn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hr : 0 < r := by dsimp [r]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨D, hD, hest⟩ := poisson_interior_estimates c hr hA hM
  refine ⟨D, hD, ?_⟩
  intro lam Aσ σ hi hp hb hm hcap
  have hsub : Metric.closedBall c (3*r) ⊆ V := closedBall_eighth_subset_annulus hc
  have hV : V ⊆ {x : Position | x ≠ 0} := by
    intro x hx hz
    have hh := hx.1
    rw [hz, norm_zero] at hh
    linarith
  have h3 : Metric.ball c (3*r) ⊆ {x : Position | x ≠ 0} :=
    (Metric.ball_subset_closedBall.trans hsub).trans hV
  have h2 : Metric.ball c (2*r) ⊆ {x : Position | x ≠ 0} :=
    (Metric.ball_subset_ball (by linarith : 2*r ≤ 3*r)).trans h3
  have hCB : Metric.closedBall c (2*r) ⊆ V :=
    (Metric.closedBall_subset_closedBall (by linarith : 2*r ≤ 3*r)).trans hsub
  have hcont := screenedField_continuousOn hi hp hb (lam := lam)
  apply hest (screenedField lam σ) σ (hcont.mono h3)
    ((screenedField_weakLaplacian hi hp hb).mono h2) hi hp
    (fun x hx => (hcap x (hsub hx).1 (hsub hx).2).2)
  have hint : IntegrableOn (fun x => ‖screenedField lam σ x‖) V :=
    (hcont.mono hV).norm.integrableOn_compact (isCompact_closedNormAnnulus _ _)
  calc
    (∫ x in Metric.closedBall c (2*r), ‖screenedField lam σ x‖) ≤
        ∫ x in V, ‖screenedField lam σ x‖ :=
      setIntegral_mono_set hint (Filter.Eventually.of_forall (fun x => norm_nonneg _))
        (Filter.Eventually.of_forall hCB)
    _ ≤ M := by
      exact neutral_annulus_lone_bound hi hp hb hm (by positivity) hC
        (fun x hxa hxb => (hcap x hxa hxb).1)

theorem neutral_screened_precompact_sequence
    {σ : ℕ → Position → ℝ} {lam Aσ : ℕ → ℝ} {C : ℝ}
    (hσi : ∀ n, Integrable (σ n)) (hσp : ∀ n x, 0 ≤ σ n x)
    (hσbd : ∀ n x, σ n x ≤ Aσ n) (hmass : ∀ n, (∫ x, σ n x) = lam n)
    (hC : 0 ≤ C)
    (hband : ∀ a b : ℝ, 0 < a → a < b → ∃ A : ℝ, 0 ≤ A ∧
      ∀ᶠ n in atTop, ∀ x : Position, a ≤ ‖x‖ → ‖x‖ ≤ b →
        screenedField (lam n) (σ n) x ≤ C/‖x‖^4 ∧ σ n x ≤ A) :
    ∃ (F : Position → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      ContinuousOn F {x | x ≠ 0} ∧
      TendstoLocallyUniformlyOn (fun n => screenedField (lam (φ n)) (σ (φ n))) F atTop {x | x ≠ 0} ∧
      LocallyLipschitzOn Set.univ (fun x : PuncturedPosition => F x) := by
  let : LocallyCompactSpace PuncturedPosition :=
    (isOpen_ne : IsOpen {x : Position | x ≠ 0}).locallyCompactSpace
  let G : ℕ → PuncturedPosition → ℝ := fun n x => screenedField (lam n) (σ n) x
  have hGc : ∀ n, Continuous (G n) := fun n =>
    continuousOn_iff_continuous_domRestrict.mp
      (screenedField_continuousOn (hσi n) (hσp n) (hσbd n))
  have hGe : ∀ x : PuncturedPosition, ∃ (r D : ℝ) (N : ℕ), 0 < r ∧ 0 ≤ D ∧
      ∀ n, N ≤ n → ‖G n x‖ ≤ D ∧
        ∀ y ∈ Metric.ball x r, ∀ z ∈ Metric.ball x r, ‖G n y-G n z‖ ≤ D*dist y z := by
    intro x
    have hn : 0 < ‖x.val‖ := norm_pos_iff.mpr x.property
    obtain ⟨A, hA, hEv⟩ := hband (‖x.val‖/2) (2*‖x.val‖) (by positivity) (by linarith)
    obtain ⟨D, hD, hEst⟩ := neutral_screened_ball_estimates x.property hC hA
    obtain ⟨N, hN⟩ := eventually_atTop.mp hEv
    refine ⟨‖x.val‖/8, D, N, by positivity, hD.le, ?_⟩
    intro n hn'
    obtain ⟨hv, hl⟩ := hEst (lam n) (Aσ n) (σ n) (hσi n) (hσp n) (hσbd n) (hmass n) (hN n hn')
    constructor
    · exact hv x (Metric.mem_closedBall_self (by positivity))
    · intro y hy z hz
      have hy' : y.val ∈ Metric.closedBall x.val (‖x.val‖/8) := Metric.mem_closedBall.mpr hy.le
      have hz' : z.val ∈ Metric.closedBall x.val (‖x.val‖/8) := Metric.mem_closedBall.mpr hz.le
      simpa only [G, Subtype.dist_eq, dist_eq_norm] using hl y hy' z hz'
  obtain ⟨f, φ, hφ, hu, hl⟩ := locallyUniform_subsequence_of_eventual_ball_estimates G hGc hGe
  refine ⟨extendPunctured f, φ, hφ, ?_, ?_, ?_⟩
  · apply continuousOn_iff_continuous_domRestrict.mpr
    change Continuous (fun x : PuncturedPosition => extendPunctured f x)
    simpa only [extendPunctured_val] using f.continuous
  · apply tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mpr
    change TendstoLocallyUniformly (fun n (x : PuncturedPosition) =>
      screenedField (lam (φ n)) (σ (φ n)) x)
      (fun x : PuncturedPosition => extendPunctured f x) atTop
    simpa only [extendPunctured_val, G] using hu
  · simpa only [extendPunctured_val] using hl

theorem tendsto_integral_mul_test_of_locallyUniformlyOn
    {F : ℕ → Position → ℝ} {f ψ : Position → ℝ} {U : Set Position}
    (hF : ∀ n, LocallyIntegrableOn (F n) U) (hf : ContinuousOn f U)
    (hu : TendstoLocallyUniformlyOn F f atTop U)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (ht : tsupport ψ ⊆ U) :
    Tendsto (fun n => ∫ x, F n x * ψ x) atTop (𝓝 (∫ x, f x * ψ x)) := by
  have hu' := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hc).mp (hu.mono ht)
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuousOn (hf.mono ht)
  have hbd : ∀ᶠ n in atTop, ∀ x ∈ tsupport ψ, ‖F n x‖ ≤ max M 0+1 := by
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hu') 1 (by norm_num)] with n hn x hx
    calc
      ‖F n x‖ ≤ ‖F n x-f x‖+‖f x‖ := norm_le_norm_sub_add _ _
      _ ≤ 1+M := add_le_add (by simpa only [dist_comm, dist_eq_norm] using (hn x hx).le) (hM x hx)
      _ ≤ max M 0+1 := by linarith [le_max_left M 0]
  apply tendsto_integral_filter_of_dominated_convergence (fun x => (max M 0+1)*‖ψ x‖)
  · exact Filter.Eventually.of_forall fun n => (integrable_mul_test_on (hF n) hψ hc ht).aestronglyMeasurable
  · filter_upwards [hbd] with n hn
    exact Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ tsupport ψ
      · simpa only [norm_mul] using mul_le_mul_of_nonneg_right (hn x hx) (norm_nonneg (ψ x))
      · simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero, norm_zero, le_refl]
  · exact (hψ.norm.integrable_of_hasCompactSupport hc.norm).const_mul _
  · exact Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ tsupport ψ
      · exact (hu'.tendsto_at hx).mul_const (ψ x)
      · simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero]
        exact tendsto_const_nhds

theorem continuous_comp_locallyUniformlyOn
    {F : ℕ → Position → ℝ} {f : Position → ℝ} {U : Set Position} {g : ℝ → ℝ}
    (hu : TendstoLocallyUniformlyOn F f atTop U) (hf : ContinuousOn f U)
    (hg : Continuous g) :
    TendstoLocallyUniformlyOn (fun n x => g (F n x)) (fun x => g (f x)) atTop U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto]
  intro x hx
  have hj : Tendsto (fun z : ℕ × Position => F z.1 z.2)
      (atTop ×ˢ 𝓝[U] x) (𝓝 (f x)) := by
    apply tendsto_comp_of_locally_uniform_limit_within (hf x hx) tendsto_snd
    intro v hv
    obtain ⟨t, ht, hFt⟩ := hu v hv x hx
    exact ⟨t, ht, tendsto_fst.eventually hFt⟩
  have hf' : Tendsto (fun z : ℕ × Position => f z.2)
      (atTop ×ˢ 𝓝[U] x) (𝓝 (f x)) := Filter.Tendsto.comp (hf x hx) tendsto_snd
  exact ((hg.continuousAt.tendsto.comp hf').prodMk_nhds
    (hg.continuousAt.tendsto.comp hj)).mono_right (nhds_le_uniformity _)

theorem HasWeakLaplacian.locallyUniformLimit
    {Fn qn : ℕ → Position → ℝ} {F q : Position → ℝ} {U : Set Position}
    (hU : IsOpen U) (hFc : ∀ n, ContinuousOn (Fn n) U)
    (hqc : ∀ n, LocallyIntegrableOn (qn n) U)
    (hF : ContinuousOn F U) (hq : ContinuousOn q U)
    (hFu : TendstoLocallyUniformlyOn Fn F atTop U)
    (hqu : TendstoLocallyUniformlyOn qn q atTop U)
    (hw : ∀ n, HasWeakLaplacian (Fn n) U (qn n)) : HasWeakLaplacian F U q := by
  intro φ hφ hc ht
  have hl := tendsto_integral_mul_test_of_locallyUniformlyOn
    (fun n => (hFc n).locallyIntegrableOn hU.measurableSet) hF hFu
    (continuous_coordinateLaplacian (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top)))
    (hasCompactSupport_coordinateLaplacian hc) ((tsupport_coordinateLaplacian_subset φ).trans ht)
  have hr := tendsto_integral_mul_test_of_locallyUniformlyOn hqc hq hqu hφ.continuous hc ht
  exact tendsto_nhds_unique
    (hl.congr' (Filter.Eventually.of_forall fun n => hw n φ hφ hc ht)) hr

theorem tfDensityScalar_continuous : Continuous tfDensityScalar := by
  exact continuous_const.mul ((Real.continuous_rpow_const (by norm_num : (0:ℝ)≤3/2)).comp
    (continuous_id.max continuous_const))

theorem density_locallyUniform_of_vanishing_error
    {Fn σn : ℕ → Position → ℝ} {F : Position → ℝ} {U : Set Position}
    (hFu : TendstoLocallyUniformlyOn Fn F atTop U) (hF : ContinuousOn F U)
    (he : TendstoLocallyUniformlyOn (fun n x => σn n x-tfDensityScalar (Fn n x))
      (fun _ => 0) atTop U) :
    TendstoLocallyUniformlyOn σn (fun x => tfDensityScalar (F x)) atTop U := by
  have hh := he.add (continuous_comp_locallyUniformlyOn hFu hF tfDensityScalar_continuous)
  change TendstoLocallyUniformlyOn (fun n x => σn n x-tfDensityScalar (Fn n x)+tfDensityScalar (Fn n x))
    (fun x => 0+tfDensityScalar (F x)) atTop U at hh
  simpa only [sub_add_cancel, zero_add] using hh

theorem screened_semilinear_limit
    {σn : ℕ → Position → ℝ} {lam A : ℕ → ℝ} {F : Position → ℝ}
    (hσi : ∀ n, Integrable (σn n)) (hσp : ∀ n x, 0 ≤ σn n x)
    (hσbd : ∀ n x, σn n x ≤ A n)
    (hF : ContinuousOn F {x | x ≠ 0})
    (hFu : TendstoLocallyUniformlyOn (fun n => screenedField (lam n) (σn n)) F atTop {x | x ≠ 0})
    (he : TendstoLocallyUniformlyOn
      (fun n x => σn n x-tfDensityScalar (screenedField (lam n) (σn n) x))
      (fun _ => 0) atTop {x | x ≠ 0}) :
    HasWeakLaplacian F {x | x ≠ 0} (fun x => tfReaction (F x)) := by
  have hσu := density_locallyUniform_of_vanishing_error hFu hF he
  have hqu := continuous_comp_locallyUniformlyOn (g := fun t : ℝ => (4*Real.pi)*t) hσu
    (tfDensityScalar_continuous.comp_continuousOn hF) (continuous_const.mul continuous_id)
  have hqr : TendstoLocallyUniformlyOn (fun n x => (4*Real.pi)*σn n x)
      (fun x => tfReaction (F x)) atTop {x | x ≠ 0} := by
    convert hqu using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    simp only [tfReaction, tfDensityScalar]
    ring
  exact HasWeakLaplacian.locallyUniformLimit isOpen_ne
    (fun n => screenedField_continuousOn (hσi n) (hσp n) (hσbd n))
    (fun n => ((hσi n).const_mul (4*Real.pi)).locallyIntegrable.locallyIntegrableOn _)
    hF (tfReaction_continuous.comp_continuousOn hF) hFu hqr
    (fun n => screenedField_weakLaplacian (hσi n) (hσp n) (hσbd n))

theorem poisson_interior_estimates_uniform {r A M : ℝ}
    (hr : 0 < r) (hA : 0 ≤ A) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : Position) (F σ : Position → ℝ),
      ContinuousOn F (Metric.ball c (3*r)) →
      HasWeakLaplacian F (Metric.ball c (2*r)) (fun x => 4*Real.pi*σ x) →
      IntegrableOn σ (Metric.closedBall c (3*r)) →
      (∀ x ∈ Metric.closedBall c (3*r), 0 ≤ σ x) →
      (∀ x ∈ Metric.closedBall c (3*r), σ x ≤ A) →
      (∫ x in Metric.closedBall c (2*r), ‖F x‖) ≤ M →
      (∀ z ∈ Metric.closedBall c r, ‖F z‖ ≤ C) ∧
      (∀ z ∈ Metric.closedBall c r, ∀ z' ∈ Metric.closedBall c r,
        ‖F z-F z'‖ ≤ C*‖z-z'‖) := by
  obtain ⟨HC, hHC, hest⟩ := harmonic_interior_estimates_local hr
  let V := (volume (Metric.closedBall (0 : Position) (3*r))).toReal
  let V' := (volume (Metric.closedBall (0 : Position) (2*r))).toReal
  let PB := A*(∫ y in Metric.ball (0 : Position) 1, coulombKernel y)+A*V
  let LB := A*(∫ y in Metric.ball (0 : Position) 1, (coulombKernel y)^2)+A*V
  have hPB : 0 ≤ PB := add_nonneg (mul_nonneg hA (integral_nonneg coulombKernel_nonneg))
    (mul_nonneg hA ENNReal.toReal_nonneg)
  have hLB : 0 ≤ LB := add_nonneg (mul_nonneg hA (integral_nonneg (fun y => sq_nonneg _)))
    (mul_nonneg hA ENNReal.toReal_nonneg)
  let H := M+PB*V'
  have hH : 0 ≤ H := add_nonneg hM (mul_nonneg hPB ENNReal.toReal_nonneg)
  let C := HC*H+PB+LB+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro c F σ hF hpoisson hσ hσpos hσbd hIF
  let W := Metric.closedBall c (3*r)
  let W' := Metric.closedBall c (2*r)
  have hV : (volume W).toReal = V := by
    simp only [W, V, EuclideanSpace.volume_closedBall]
  have hV' : (volume W').toReal = V' := by
    simp only [W', V', EuclideanSpace.volume_closedBall]
  let ρ := W.indicator σ
  have hρ : Integrable ρ := (integrable_indicator_iff measurableSet_closedBall).mpr hσ
  have hρpos : ∀ x, 0 ≤ ρ x := fun x => Set.indicator_nonneg hσpos x
  have hρbd : ∀ x, ρ x ≤ A := by
    intro x
    by_cases hx : x ∈ W
    · simpa only [ρ, Set.indicator_of_mem hx] using hσbd x hx
    · simpa only [ρ, Set.indicator_of_notMem hx] using hA
  have hmass : (∫ x, ρ x) ≤ A*V := by
    rw [show ρ = W.indicator σ from rfl, integral_indicator measurableSet_closedBall]
    calc
      (∫ x in W, σ x) ≤ ∫ _ in W, A := integral_mono_ae hσ
        (integrableOn_const (isCompact_closedBall c (3*r)).measure_ne_top)
        ((ae_restrict_mem measurableSet_closedBall).mono (fun x hx => hσbd x hx))
      _ = A*V := by simp only [integral_const, Measure.restrict_apply_univ, smul_eq_mul,
          measureReal_def, hV, mul_comm]
  let P := potentialOf ρ
  have hPcont : Continuous P := potentialOf_continuous hρ hρpos hρbd
  have hPbd (x : Position) : ‖P x‖ ≤ PB := by
    have hp : 0 ≤ P x := integral_nonneg (fun y => mul_nonneg (coulombKernel_nonneg _) (hρpos y))
    rw [Real.norm_eq_abs, abs_of_nonneg hp]
    exact (bounded_density_convolution measurable_coulombKernel coulombKernel_nonneg
      (coulombKernel_integrableOn_ball 1) (fun _ => coulombKernel_le_one)
      hρ hρpos hρbd x).2.trans (by dsimp only [PB]; linarith)
  have hPlip (x y : Position) : ‖P x-P y‖ ≤ LB*‖x-y‖ :=
    (potentialOf_lipschitz_bound hρ hρpos hρbd x y).trans
      (mul_le_mul_of_nonneg_right (by dsimp only [LB]; linarith) (norm_nonneg _))
  have hW' : W' ⊆ Metric.ball c (3*r) := by
    intro x hx
    change dist x c ≤ 2*r at hx
    change dist x c < 3*r
    linarith
  have hball : Metric.ball c (2*r) ⊆ Metric.ball c (3*r) :=
    Metric.ball_subset_ball (by linarith)
  let h : Position → ℝ := fun x => F x+P x
  have hhcont : ContinuousOn h (Metric.ball c (3*r)) := hF.add hPcont.continuousOn
  have hharm : HasWeakLaplacian h (Metric.ball c (2*r)) (fun _ => 0) :=
    local_harmonic_part Metric.isOpen_ball (hF.mono hball) hpoisson hρ hρpos hρbd (by
      intro x hx
      have hxW : x ∈ W := by
        change dist x c ≤ 3*r
        exact (hball hx).le
      exact (Set.indicator_of_mem hxW σ).symm)
  have hiF : IntegrableOn (fun x => ‖F x‖) W' :=
    ((hF.mono hW').norm).integrableOn_compact (isCompact_closedBall c (2*r))
  have hih : IntegrableOn (fun x => ‖h x‖) W' :=
    ((hhcont.mono hW').norm).integrableOn_compact (isCompact_closedBall c (2*r))
  have hiPB : IntegrableOn (fun _ : Position => PB) W' :=
    integrableOn_const (isCompact_closedBall c (2*r)).measure_ne_top
  have hIh : (∫ x in W', ‖h x‖) ≤ H := by
    calc
      (∫ x in W', ‖h x‖) ≤ ∫ x in W', ‖F x‖+PB := integral_mono_ae hih (hiF.add hiPB)
        (Filter.Eventually.of_forall (fun x => (norm_add_le (F x) (P x)).trans
          (add_le_add le_rfl (hPbd x))))
      _ = (∫ x in W', ‖F x‖)+PB*V' := by
        rw [integral_add hiF hiPB, integral_const]
        simp only [Measure.restrict_apply_univ, smul_eq_mul, measureReal_def, hV', mul_comm]
      _ ≤ H := by dsimp only [H]; linarith
  obtain ⟨hval, hdiff⟩ := hest c h hhcont hharm
  have hCval : HC*H+PB ≤ C := by dsimp [C]; linarith
  have hClip : HC*H+LB ≤ C := by dsimp [C]; linarith
  constructor
  · intro z hz
    calc
      ‖F z‖ = ‖h z-P z‖ := by dsimp [h]; rw [add_sub_cancel_right]
      _ ≤ ‖h z‖+‖P z‖ := norm_sub_le _ _
      _ ≤ HC*(∫ x in W', ‖h x‖)+PB := add_le_add (hval z hz) (hPbd z)
      _ ≤ HC*H+PB := by linarith [mul_le_mul_of_nonneg_left hIh hHC.le]
      _ ≤ C := hCval
  · intro z hz z' hz'
    calc
      ‖F z-F z'‖ = ‖(h z-h z')-(P z-P z')‖ := by congr 1; dsimp [h]; ring
      _ ≤ ‖h z-h z'‖+‖P z-P z'‖ := norm_sub_le _ _
      _ ≤ HC*(∫ x in W', ‖h x‖)*‖z-z'‖+LB*‖z-z'‖ :=
        add_le_add (hdiff z hz z' hz') (hPlip z z')
      _ ≤ (HC*H+LB)*‖z-z'‖ := by
        have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hIh hHC.le)
          (norm_nonneg (z-z'))
        nlinarith
      _ ≤ C*‖z-z'‖ := mul_le_mul_of_nonneg_right hClip (norm_nonneg _)

theorem tendsto_integral_norm_on_compact_of_locallyUniformlyOn
    {Fn : ℕ → Position → ℝ} {F : Position → ℝ} {U K : Set Position}
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hFn : ∀ n, ContinuousOn (Fn n) U) (hF : ContinuousOn F U)
    (hu : TendstoLocallyUniformlyOn Fn F atTop U) :
    Tendsto (fun n => ∫ x in K, ‖Fn n x‖) atTop (𝓝 (∫ x in K, ‖F x‖)) := by
  have hu' := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp (hu.mono hKU)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hF.mono hKU)
  have hbd : ∀ᶠ n in atTop, ∀ x ∈ K, ‖Fn n x‖ ≤ max M 0+1 := by
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hu') 1 (by norm_num)] with n hn x hx
    calc
      ‖Fn n x‖ ≤ ‖Fn n x-F x‖+‖F x‖ := norm_le_norm_sub_add _ _
      _ ≤ 1+M := add_le_add (by simpa only [dist_comm, dist_eq_norm] using (hn x hx).le) (hM x hx)
      _ ≤ max M 0+1 := by linarith [le_max_left M 0]
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => max M 0+1)
  · exact Filter.Eventually.of_forall fun n =>
      ((hFn n).mono hKU).norm.aestronglyMeasurable hK.measurableSet
  · filter_upwards [hbd] with n hn
    exact (ae_restrict_mem hK.measurableSet).mono fun x hx => by
      simpa only [norm_norm] using hn x hx
  · exact integrableOn_const hK.measure_ne_top
  · exact (ae_restrict_mem hK.measurableSet).mono fun x hx => (hu'.tendsto_at hx).norm

theorem smul_closedNormAnnulus {D : ℝ} (hD : 0 < D) (a b : ℝ) :
    D • closedNormAnnulus a b = closedNormAnnulus (D*a) (D*b) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hD.ne']
  simp only [closedNormAnnulus, Set.mem_ofPred_eq, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hD), ← div_eq_inv_mul]
  constructor
  · rintro ⟨h1,h2⟩
    exact ⟨by simpa only [mul_comm] using (le_div_iff₀ hD).mp h1,
      by simpa only [mul_comm] using (div_le_iff₀ hD).mp h2⟩
  · rintro ⟨h1,h2⟩
    exact ⟨(le_div_iff₀ hD).mpr (by simpa only [mul_comm] using h1),
      (div_le_iff₀ hD).mpr (by simpa only [mul_comm] using h2)⟩

theorem volume_closedNormAnnulus_dilate {D : ℝ} (hD : 0 < D) (a b : ℝ) :
    (volume (closedNormAnnulus (D*a) (D*b))).toReal =
      D^3*(volume (closedNormAnnulus a b)).toReal := by
  have hh := Measure.setIntegral_comp_smul_of_pos volume (fun _ : Position => (1 : ℝ))
    (closedNormAnnulus a b) hD
  simp only [smul_closedNormAnnulus hD, Position, finrank_euclideanSpace_fin,
    integral_const, Measure.restrict_apply_univ, smul_eq_mul, mul_one, measureReal_def] at hh
  rw [hh]
  field_simp

theorem dilate_annular_lone_bound {F : Position → ℝ} {C D a b : ℝ}
    (hD : 0 < D) (ha : 0 < a)
    (hL : (∫ x in closedNormAnnulus (D*a) (D*b), ‖F x‖) ≤
      2*(C/(D*a)^4)*(volume (closedNormAnnulus (D*a) (D*b))).toReal) :
    (∫ x in closedNormAnnulus a b, ‖D^4*F (D • x)‖) ≤
      2*(C/a^4)*(volume (closedNormAnnulus a b)).toReal := by
  simp_rw [norm_mul, Real.norm_eq_abs (D^4), abs_of_nonneg (pow_nonneg hD.le 4),
    integral_const_mul]
  rw [Measure.setIntegral_comp_smul_of_pos volume (fun x => ‖F x‖) (closedNormAnnulus a b) hD]
  simp only [Position, finrank_euclideanSpace_fin, smul_eq_mul, smul_closedNormAnnulus hD]
  calc
    D^4*((D^3)⁻¹*(∫ x in closedNormAnnulus (D*a) (D*b), ‖F x‖)) ≤
      D^4*((D^3)⁻¹*(2*(C/(D*a)^4)*(volume (closedNormAnnulus (D*a) (D*b))).toReal)) := by
        gcongr
    _ = 2*(C/a^4)*(volume (closedNormAnnulus a b)).toReal := by
      rw [volume_closedNormAnnulus_dilate hD]
      field_simp

theorem neutral_screened_limit_annular_lone
    {σn : ℕ → Position → ℝ} {lam A : ℕ → ℝ} {F : Position → ℝ} {C a b : ℝ}
    (hC : 0 ≤ C) (ha : 0 < a)
    (hσi : ∀ n, Integrable (σn n)) (hσp : ∀ n x, 0 ≤ σn n x)
    (hσbd : ∀ n x, σn n x ≤ A n) (hmass : ∀ n, (∫ x, σn n x) = lam n)
    (hF : ContinuousOn F {x | x ≠ 0})
    (hFu : TendstoLocallyUniformlyOn (fun n => screenedField (lam n) (σn n)) F atTop {x | x ≠ 0})
    (hcap : ∀ᶠ n in atTop, ∀ x ∈ closedNormAnnulus a b,
      screenedField (lam n) (σn n) x ≤ C/‖x‖^4) :
    (∫ x in closedNormAnnulus a b, ‖F x‖) ≤
      2*(C/a^4)*(volume (closedNormAnnulus a b)).toReal := by
  have hK : IsCompact (closedNormAnnulus a b) := isCompact_closedNormAnnulus a b
  have hKU : closedNormAnnulus a b ⊆ {x : Position | x ≠ 0} := by
    intro x hx hz
    have hh := hx.1
    rw [hz, norm_zero] at hh
    linarith
  have ht := tendsto_integral_norm_on_compact_of_locallyUniformlyOn hK hKU
    (fun n => screenedField_continuousOn (hσi n) (hσp n) (hσbd n)) hF hFu
  apply le_of_tendsto ht
  filter_upwards [hcap] with n hn
  exact neutral_annulus_lone_bound (hσi n) (hσp n) (hσbd n) (hmass n) ha hC
    (fun x hxa hxb => hn x ⟨hxa,hxb⟩)

end NeutralAtom
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_RetainedAnalyticSequence
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open ContinuousLinearMap
open scoped Topology BigOperators ContDiff Convolution Pointwise ENNReal
namespace NeutralAtom

theorem tfDensityScalar_nonneg (t : ℝ) : 0 ≤ tfDensityScalar t :=
  mul_nonneg kTF_pos.le (Real.rpow_nonneg (le_max_right t 0) _)

theorem tfDensityScalar_monotone : Monotone tfDensityScalar := by
  intro s t hst
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (le_max_right s 0) (max_le_max_right 0 hst) (by norm_num)) kTF_pos.le

theorem semilinear_dilate {F : Position → ℝ} {D : ℝ} (hD : 0 < D)
    (hw : HasWeakLaplacian F {x | x ≠ 0} (fun x => tfReaction (F x))) :
    HasWeakLaplacian (fun x => D^4*F (D • x)) {x | x ≠ 0}
      (fun x => tfReaction (D^4*F (D • x))) := by
  have hh := hw.dilate hD
  have hU : ((fun x : Position => D • x) ⁻¹' {x | x ≠ 0}) = {x | x ≠ 0} := by
    ext x
    change D • x ≠ 0 ↔ x ≠ 0
    exact ⟨fun hx => (smul_ne_zero_iff.mp hx).2, fun hx => smul_ne_zero hD.ne' hx⟩
  rw [hU] at hh
  simpa only [tfReaction_dilate hD] using hh

theorem continuousOn_dilate {F : Position → ℝ} {D : ℝ} (hD : 0 < D)
    (hF : ContinuousOn F {x | x ≠ 0}) :
    ContinuousOn (fun x => D^4*F (D • x)) {x | x ≠ 0} := by
  apply continuousOn_const.mul
  exact hF.comp (continuous_id.const_smul D).continuousOn
    (fun x hx => smul_ne_zero hD.ne' hx)

theorem dilate_cap {F : Position → ℝ} {D C : ℝ} (hD : 0 < D)
    (hcap : ∀ x ≠ 0, F x ≤ C/‖x‖^4) :
    ∀ x ≠ 0, D^4*F (D • x) ≤ C/‖x‖^4 := by
  intro x hx
  calc
    D^4*F (D • x) ≤ D^4*(C/‖D • x‖^4) :=
      mul_le_mul_of_nonneg_left (hcap _ (smul_ne_zero hD.ne' hx)) (pow_nonneg hD.le 4)
    _ = C/‖x‖^4 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hD]
      field_simp

theorem semilinear_absolute_bound {F : Position → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hF : ContinuousOn F {x | x ≠ 0})
    (hw : HasWeakLaplacian F {x | x ≠ 0} (fun x => tfReaction (F x)))
    (hcap : ∀ x ≠ 0, F x ≤ C/‖x‖^4)
    (hL : ∀ a b : ℝ, 0 < a → (∫ x in closedNormAnnulus a b, ‖F x‖) ≤
      2*(C/a^4)*(volume (closedNormAnnulus a b)).toReal) :
    ∃ K : ℝ, 0 < K ∧ ∀ x ≠ 0, ‖F x‖ ≤ K/‖x‖^4 := by
  let V := closedNormAnnulus (1/2) 2
  let A := tfDensityScalar (C/(1/2)^4)
  let M := 2*(C/(1/2)^4)*(volume V).toReal
  have hA : 0 ≤ A := tfDensityScalar_nonneg _
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  obtain ⟨K, hK, hest⟩ := poisson_interior_estimates_uniform
    (r := 1/8) (by norm_num) hA hM
  have hunit : ∀ D : ℝ, 0 < D → ∀ c : Position, ‖c‖ = 1 → ‖D^4*F (D • c)‖ ≤ K := by
    intro D hD c hc
    let G : Position → ℝ := fun x => D^4*F (D • x)
    let σ : Position → ℝ := fun x => tfDensityScalar (G x)
    have hc0 : c ≠ 0 := by intro he; simp only [he, norm_zero] at hc; norm_num at hc
    have hsub : Metric.closedBall c (3*(1/8)) ⊆ V := by
      simpa only [hc, one_div, V, closedNormAnnulus, mul_one] using closedBall_eighth_subset_annulus hc0
    have hV : V ⊆ {x : Position | x ≠ 0} := by
      intro x hx hz
      have hh := hx.1
      rw [hz, norm_zero] at hh
      norm_num at hh
    have h3 : Metric.ball c (3*(1/8)) ⊆ {x : Position | x ≠ 0} :=
      (Metric.ball_subset_closedBall.trans hsub).trans hV
    have h2 : Metric.ball c (2*(1/8)) ⊆ {x : Position | x ≠ 0} :=
      (Metric.ball_subset_ball (by norm_num : (2:ℝ)*(1/8) ≤ 3*(1/8))).trans h3
    have hCB : Metric.closedBall c (2*(1/8)) ⊆ V :=
      (Metric.closedBall_subset_closedBall (by norm_num : (2:ℝ)*(1/8) ≤ 3*(1/8))).trans hsub
    have hGc : ContinuousOn G {x | x ≠ 0} := continuousOn_dilate hD hF
    have hσc : ContinuousOn σ {x | x ≠ 0} := tfDensityScalar_continuous.comp_continuousOn hGc
    have hσi : IntegrableOn σ (Metric.closedBall c (3*(1/8))) :=
      (hσc.mono (hsub.trans hV)).integrableOn_compact (isCompact_closedBall _ _)
    have hσp : ∀ x ∈ Metric.closedBall c (3*(1/8)), 0 ≤ σ x :=
      fun x _ => tfDensityScalar_nonneg _
    have hσbd : ∀ x ∈ Metric.closedBall c (3*(1/8)), σ x ≤ A := by
      intro x hx
      apply tfDensityScalar_monotone
      exact (dilate_cap hD hcap x (hV (hsub hx))).trans
        (div_le_div_of_nonneg_left hC (by norm_num)
          (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) (hsub hx).1 4))
    have hGw : HasWeakLaplacian G (Metric.ball c (2*(1/8))) (fun x => 4*Real.pi*σ x) := by
      have hh := (semilinear_dilate hD hw).mono h2
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      funext x
      simp only [σ, G, tfDensityScalar, tfReaction]
      ring
    have hIF : (∫ x in Metric.closedBall c (2*(1/8)), ‖G x‖) ≤ M := by
      calc
        (∫ x in Metric.closedBall c (2*(1/8)), ‖G x‖) ≤ ∫ x in V, ‖G x‖ :=
          setIntegral_mono_set ((hGc.mono hV).norm.integrableOn_compact
            (isCompact_closedNormAnnulus _ _)) (Filter.Eventually.of_forall fun x => norm_nonneg _)
            (Filter.Eventually.of_forall hCB)
        _ ≤ M := dilate_annular_lone_bound hD (by norm_num : (0:ℝ)<1/2)
          (hL (D*(1/2)) (D*2) (by positivity))
    exact (hest c G σ (hGc.mono h3) hGw hσi hσp hσbd hIF).1 c
      (Metric.mem_closedBall_self (by norm_num))
  refine ⟨K,hK,?_⟩
  intro x hx
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let c : Position := ‖x‖⁻¹ • x
  have hc : ‖c‖ = 1 := by
    change ‖‖x‖⁻¹ • x‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  have he : ‖x‖ • c = x := by
    change ‖x‖ • (‖x‖⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have hb := hunit ‖x‖ hn c hc
  rw [he, norm_mul, Real.norm_eq_abs (‖x‖^4), abs_of_nonneg (pow_nonneg hn.le 4)] at hb
  exact (le_div_iff₀ (pow_pos hn 4)).mpr (by simpa only [mul_comm] using hb)

theorem eventual_barrier_boundary
    {Fn Un Ln : ℕ → Position → ℝ} {F : Position → ℝ} {a : ℕ → ℝ}
    {Cinv K S : ℝ} (hS : 0 < S)
    (hu : TendstoLocallyUniformlyOn Fn F atTop {x | x ≠ 0})
    (ha : Tendsto a atTop (𝓝 0))
    (hF : ∀ x ≠ 0, ‖F x‖ ≤ K/‖x‖^4)
    (hU : ∀ n x, a n ≤ ‖x‖ → Un n x ≤ Cinv/‖x‖^4)
    (hL : ∀ n x, 0 ≤ Ln n x) :
    ∀ᶠ n in atTop, ∀ x : Position, ‖x‖ = S →
      Un n x-Fn n x-Ln n x-(Cinv+K+1)/S^4 ≤ 0 := by
  have hsub : Metric.sphere (0 : Position) S ⊆ {x | x ≠ 0} := by
    intro x hx hz
    have hh : ‖x‖ = S := by simpa only [Metric.mem_sphere, dist_zero_right] using hx
    subst x
    simp only [norm_zero] at hh
    linarith
  have hu' := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
    (isCompact_sphere (0 : Position) S)).mp (hu.mono hsub)
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hu') (1/S^4) (by positivity),
    ha.eventually (gt_mem_nhds hS)] with n hn han x hx
  have hxs : x ∈ Metric.sphere (0 : Position) S := by simpa only [Metric.mem_sphere, dist_zero_right] using hx
  have hx0 := hsub hxs
  have he : ‖Fn n x-F x‖ ≤ 1/S^4 := by
    simpa only [dist_comm, dist_eq_norm] using (hn x hxs).le
  have hfn : ‖Fn n x‖ ≤ (K+1)/S^4 := by
    calc
      ‖Fn n x‖ ≤ ‖Fn n x-F x‖+‖F x‖ := norm_le_norm_sub_add _ _
      _ ≤ 1/S^4+K/S^4 := add_le_add he (by simpa only [hx] using hF x hx0)
      _ = (K+1)/S^4 := by ring
  have hus : Un n x ≤ Cinv/S^4 := by
    simpa only [hx] using hU n x (by rw [hx]; exact han.le)
  have hneg : -Fn n x ≤ ‖Fn n x‖ := by simpa only [Real.norm_eq_abs] using neg_le_abs (Fn n x)
  have hls := hL n x
  have hc : (Cinv+K+1)/S^4 = Cinv/S^4+(K+1)/S^4 := by ring
  rw [hc]
  linarith

theorem barrier_lower_of_eventual_comparison
    {Fn Un : ℕ → Position → ℝ} {Ln : ℝ → ℕ → Position → ℝ}
    {F : Position → ℝ} {a : ℕ → ℝ} {B H : ℝ}
    (ha : Tendsto a atTop (𝓝 0))
    (hF : ∀ x ≠ 0, Tendsto (fun n => Fn n x) atTop (𝓝 (F x)))
    (hL : ∀ S x, x ≠ 0 → Tendsto (fun n => Ln S n x) atTop (𝓝 0))
    (hU : ∀ n x, a n ≤ ‖x‖ → B/‖x‖^4*(1-a n/(8*‖x‖)) ≤ Un n x)
    (hcmp : ∀ S : ℝ, 0 < S → ∀ᶠ n in atTop,
      ∀ x ∈ Metric.closedBall (0 : Position) S, Un n x ≤ Fn n x+Ln S n x+H/S^4) :
    ∀ x ≠ 0, B/‖x‖^4 ≤ F x := by
  intro x hx
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hb : ∀ S : ℝ, ‖x‖ < S → B/‖x‖^4 ≤ F x+H/S^4 := by
    intro S hS
    have hal : ∀ᶠ n in atTop, a n ≤ ‖x‖ :=
      (ha.eventually (gt_mem_nhds hn)).mono (fun n h => h.le)
    have ht1 : Tendsto (fun n => B/‖x‖^4*(1-a n/(8*‖x‖))) atTop (𝓝 (B/‖x‖^4)) := by
      simpa only [zero_div, sub_zero, mul_one] using
        (((tendsto_const_nhds (x := (1 : ℝ))).sub (ha.div_const (8*‖x‖))).const_mul (B/‖x‖^4))
    have ht2 : Tendsto (fun n => Fn n x+Ln S n x+H/S^4) atTop (𝓝 (F x+H/S^4)) := by
      simpa only [add_zero] using ((hF x hx).add (hL S x hx)).add_const (H/S^4)
    apply le_of_tendsto_of_tendsto ht1 ht2
    filter_upwards [hal, hcmp S (hn.trans hS)] with n han hcn
    exact (hU n x han).trans (hcn x (by simpa only [Metric.mem_closedBall, dist_zero_right] using hS.le))
  have ht : Tendsto (fun S : ℝ => F x+H/S^4) atTop (𝓝 (F x)) := by
    have hh : Tendsto (fun S : ℝ => (S^4)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by decide : 4 ≠ 0))
    simpa only [div_eq_mul_inv, mul_zero, add_zero] using (hh.const_mul H).const_add (F x)
  apply ge_of_tendsto ht
  exact (eventually_gt_atTop ‖x‖).mono (fun S hS => hb S hS)

theorem correctionDensity_bound {q a S : ℝ} (ha : 0 < a) (x : Position) :
    correctionDensity q a S x ≤ (q^8)⁻¹*(a^6)⁻¹ := by
  by_cases hx : a ≤ ‖x‖ ∧ ‖x‖ ≤ S
  · have hx' : x ∈ {y : Position | a ≤ ‖y‖ ∧ ‖y‖ ≤ S} := hx
    rw [correctionDensity, Set.indicator_of_mem hx']
    exact mul_le_mul_of_nonneg_left
      (inv_anti₀ (pow_pos ha 6) (pow_le_pow_left₀ ha.le hx.1 6)) (by positivity : 0 ≤ (q^8)⁻¹)
  · have hx' : x ∉ {y : Position | a ≤ ‖y‖ ∧ ‖y‖ ≤ S} := hx
    rw [correctionDensity, Set.indicator_of_notMem hx']
    positivity

theorem potentialOf_add_bounded {ρ η : Position → ℝ} {A B : ℝ}
    (hiρ : Integrable ρ) (hpρ : ∀ x, 0 ≤ ρ x) (hbρ : ∀ x, ρ x ≤ A)
    (hiη : Integrable η) (hpη : ∀ x, 0 ≤ η x) (hbη : ∀ x, η x ≤ B) (x : Position) :
    potentialOf (ρ+η) x = potentialOf ρ x+potentialOf η x := by
  have hi1 := (potential_integrable_and_bound (x := x) hiρ hpρ (by norm_num : (0:ℝ)<1)
    (fun y _ => hbρ y)).1
  have hi2 := (potential_integrable_and_bound (x := x) hiη hpη (by norm_num : (0:ℝ)<1)
    (fun y _ => hbη y)).1
  unfold potentialOf
  simp only [Pi.add_apply, mul_add]
  exact integral_add hi1 hi2

theorem full_correction_tendsto_zero {p : ℕ → Position → ℝ} {a q Ap : ℕ → ℝ}
    (hi : ∀ n, Integrable (p n)) (hp : ∀ n x, 0 ≤ p n x)
    (hb : ∀ n x, p n x ≤ Ap n) (hs : ∀ n x, a n < ‖x‖ → p n x = 0)
    (ha : Tendsto a atTop (𝓝 0)) (hap : ∀ n, 0 < a n)
    (hm : Tendsto (fun n => ∫ x, p n x) atTop (𝓝 0))
    (hq : Tendsto q atTop atTop) (hal : ∀ᶠ n in atTop, 1/(2*q n) ≤ a n)
    (S : ℝ) {x : Position} (hx : x ≠ 0) :
    Tendsto (fun n => potentialOf (fun y => p n y+correctionDensity (q n) (a n) S y) x)
      atTop (𝓝 0) := by
  have hh := (inner_potential_tendsto_zero hi hp hs ha hm hx).add
    (correction_potential_tendsto_zero S hq hal hx)
  simp only [add_zero] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  exact potentialOf_add_bounded (hi n) (hp n) (hb n)
    (correctionDensity_integrable_and_mass (hap n)).1 (correctionDensity_nonneg _ _ _)
    (correctionDensity_bound (hap n)) x

theorem screened_limit_positive
    {σ U p : ℕ → Position → ℝ} {lam a q Aσ Ap : ℕ → ℝ}
    {F : Position → ℝ} {B Cinv K : ℝ}
    (hσi : ∀ n, Integrable (σ n)) (hσp : ∀ n x, 0 ≤ σ n x)
    (hσb : ∀ n x, σ n x ≤ Aσ n)
    (hpi : ∀ n, Integrable (p n)) (hpp : ∀ n x, 0 ≤ p n x)
    (hpb : ∀ n x, p n x ≤ Ap n) (hps : ∀ n x, a n < ‖x‖ → p n x = 0)
    (hpm : Tendsto (fun n => ∫ x, p n x) atTop (𝓝 0))
    (hap : ∀ n, 0 < a n) (ha : Tendsto a atTop (𝓝 0))
    (hq : Tendsto q atTop atTop) (hal : ∀ᶠ n in atTop, 1/(2*q n) ≤ a n)
    (hUc : ∀ n, Continuous (fun x => U n x-lam n*coulombKernel x))
    (hUl : ∀ n x, a n ≤ ‖x‖ → B/‖x‖^4*(1-a n/(8*‖x‖)) ≤ U n x)
    (hUu : ∀ n x, a n ≤ ‖x‖ → U n x ≤ Cinv/‖x‖^4)
    (hUw : ∀ n, WeakNuclearSubsolution (U n) (lam n) Set.univ (barrierSource (a n) (U n) (σ n) (p n)))
    (hband : ∀ n x, a n ≤ ‖x‖ → ‖x‖ ≤ q n →
      |σ n x-tfDensityScalar (screenedField (lam n) (σ n) x)| ≤ ((q n)^8)⁻¹*(‖x‖^6)⁻¹)
    (hu : TendstoLocallyUniformlyOn (fun n => screenedField (lam n) (σ n)) F atTop {x | x ≠ 0})
    (hK : 0 ≤ K) (hF : ∀ x ≠ 0, ‖F x‖ ≤ K/‖x‖^4) :
    ∀ x ≠ 0, B/‖x‖^4 ≤ F x := by
  let L : ℝ → ℕ → Position → ℝ := fun S n =>
    potentialOf (fun y => p n y+correctionDensity (q n) (a n) S y)
  have hLpos : ∀ S n x, 0 ≤ L S n x := fun S n x =>
    potentialOf_nonneg (fun y => add_nonneg (hpp n y) (correctionDensity_nonneg _ _ _ y)) x
  have hUb : ∀ n x, a n ≤ ‖x‖ → U n x ≤ max Cinv 0/‖x‖^4 := by
    intro n x hx
    exact (hUu n x hx).trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
  apply barrier_lower_of_eventual_comparison (H := max Cinv 0+K+1) ha
    (fun x hx => hu.tendsto_at hx) (fun S x hx =>
      full_correction_tendsto_zero hpi hpp hpb hps ha hap hpm hq hal S hx) hUl
  intro S hS
  have hbdy := eventual_barrier_boundary (Ln := L S) hS hu ha hF hUb (hLpos S)
  filter_upwards [hbdy, hq.eventually (eventually_ge_atTop S)] with n hbn hqn
  have hAU : ∀ x, a n ≤ ‖x‖ → U n x ≤ max Cinv 0/(a n)^4 := by
    intro x hx
    exact (hUb n x hx).trans (div_le_div_of_nonneg_left (le_max_right _ _)
      (pow_pos (hap n) 4) (pow_le_pow_left₀ (hap n).le hx 4))
  have hbw : WeakNuclearSubsolution (U n) (lam n) (Metric.ball 0 S)
      (barrierSource (a n) (U n) (σ n) (p n)) := by
    intro φ hφ hc ht hp
    exact hUw n φ hφ hc (fun _ _ => Set.mem_univ _) hp
  apply positive_barrier_comparison (hap n) hS (by positivity) (hUc n) hAU
    (hσi n) (hσp n) (hσb n) (hpi n) (hpp n) (hpb n)
    (correctionDensity_integrable_and_mass (hap n)).1
    (correctionDensity_nonneg _ _ _) (correctionDensity_bound (hap n)) hbw
  · intro x hx hax
    have hxS : ‖x‖ ≤ S := by
      exact (show ‖x‖ < S by simpa only [Metric.mem_ball, dist_zero_right] using hx).le
    have hb := (le_abs_self _).trans (hband n x hax (hxS.trans hqn))
    have heq : correctionDensity (q n) (a n) S x = ((q n)^8)⁻¹*(‖x‖^6)⁻¹ := by
      exact Set.indicator_of_mem (show x ∈ {y : Position | a n ≤ ‖y‖ ∧ ‖y‖ ≤ S} from ⟨hax,hxS⟩) _
    rw [heq]
    have hh := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 4*Real.pi)
    dsimp only [tfReaction, tfDensityScalar, screenedField, screenedPotential] at hh ⊢
    nlinarith only [hh]
  · exact hbn

theorem expanding_annular_error_locallyUniform
    {e : ℕ → Position → ℝ} {a q : ℕ → ℝ}
    (ha : Tendsto a atTop (𝓝 0)) (hq : Tendsto q atTop atTop)
    (hband : ∀ n x, a n ≤ ‖x‖ → ‖x‖ ≤ q n → |e n x| ≤ ((q n)^8)⁻¹*(‖x‖^6)⁻¹) :
    TendstoLocallyUniformlyOn e (fun _ => 0) atTop {x | x ≠ 0} := by
  apply Metric.tendstoLocallyUniformlyOn_iff.mpr
  intro ε hε x hx
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  refine ⟨Metric.ball x (‖x‖/4), mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x (by positivity)), ?_⟩
  have hq8 : Tendsto (fun n => ((q n)^8)⁻¹*((‖x‖/2)^6)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_mul] using
      (tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by decide : 8 ≠ 0)).comp hq)).mul_const (((‖x‖/2)^6)⁻¹)
  filter_upwards [ha.eventually (gt_mem_nhds (half_pos hn)),
    hq.eventually (eventually_ge_atTop (2*‖x‖)), hq8.eventually (gt_mem_nhds hε)] with n han hqn hen y hy
  have hy' : ‖x-y‖ < ‖x‖/4 := by simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hy
  have hyl : ‖x‖/2 ≤ ‖y‖ := by linarith [norm_le_norm_sub_add x y]
  have hyu : ‖y‖ ≤ 2*‖x‖ := by
    have hh := norm_le_norm_sub_add y x
    rw [norm_sub_rev] at hh
    linarith
  have hh := hband n y (han.le.trans hyl) (hyu.trans hqn)
  have hinv := inv_anti₀ (pow_pos (half_pos hn) 6) (pow_le_pow_left₀ (half_pos hn).le hyl 6)
  have hle := hh.trans (mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ ((q n)^8)⁻¹))
  simpa only [dist_zero_left, Real.norm_eq_abs] using hle.trans_lt hen

theorem expanding_annular_cap_limit {Fn : ℕ → Position → ℝ} {F : Position → ℝ}
    {a q : ℕ → ℝ} {C : ℝ}
    (ha : Tendsto a atTop (𝓝 0)) (hq : Tendsto q atTop atTop)
    (hcap : ∀ n x, a n ≤ ‖x‖ → ‖x‖ ≤ q n → Fn n x ≤ C/‖x‖^4)
    (hu : TendstoLocallyUniformlyOn Fn F atTop {x | x ≠ 0}) :
    ∀ x ≠ 0, F x ≤ C/‖x‖^4 := by
  intro x hx
  apply le_of_tendsto (hu.tendsto_at hx)
  filter_upwards [ha.eventually (gt_mem_nhds (norm_pos_iff.mpr hx)),
    hq.eventually (eventually_ge_atTop ‖x‖)] with n han hqn
  exact hcap n x han.le hqn

theorem expanding_annular_cap_eventually {Fn : ℕ → Position → ℝ}
    {a q : ℕ → ℝ} {C d r : ℝ} (hd : 0 < d)
    (ha : Tendsto a atTop (𝓝 0)) (hq : Tendsto q atTop atTop)
    (hcap : ∀ n x, a n ≤ ‖x‖ → ‖x‖ ≤ q n → Fn n x ≤ C/‖x‖^4) :
    ∀ᶠ n in atTop, ∀ x : Position, d ≤ ‖x‖ → ‖x‖ ≤ r → Fn n x ≤ C/‖x‖^4 := by
  filter_upwards [ha.eventually (gt_mem_nhds hd), hq.eventually (eventually_ge_atTop r)] with n han hqn x hxd hxr
  exact hcap n x (han.le.trans hxd) (hxr.trans hqn)

theorem expanding_annular_density_bound
    {Fn σ : ℕ → Position → ℝ} {a q : ℕ → ℝ} {C d r : ℝ} {f : ℝ → ℝ}
    (hf : Monotone f) (hfp : ∀ t, 0 ≤ f t) (hC : 0 ≤ C) (hd : 0 < d)
    (ha : Tendsto a atTop (𝓝 0)) (hq : Tendsto q atTop atTop)
    (hcap : ∀ n x, a n ≤ ‖x‖ → ‖x‖ ≤ q n → Fn n x ≤ C/‖x‖^4)
    (herr : ∀ n x, a n ≤ ‖x‖ → ‖x‖ ≤ q n → |σ n x-f (Fn n x)| ≤ ((q n)^8)⁻¹*(‖x‖^6)⁻¹) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ n in atTop, ∀ x : Position, d ≤ ‖x‖ → ‖x‖ ≤ r →
      Fn n x ≤ C/‖x‖^4 ∧ σ n x ≤ A := by
  refine ⟨f (C/d^4)+(d^6)⁻¹, add_nonneg (hfp _) (by positivity), ?_⟩
  filter_upwards [ha.eventually (gt_mem_nhds hd), hq.eventually (eventually_ge_atTop r),
    hq.eventually (eventually_ge_atTop 1)] with n han hqn hq1 x hxd hxr
  have hax := han.le.trans hxd
  have hxq := hxr.trans hqn
  have hfc := hcap n x hax hxq
  refine ⟨hfc, ?_⟩
  have hff := hf (hfc.trans (div_le_div_of_nonneg_left hC (pow_pos hd 4)
    (pow_le_pow_left₀ hd.le hxd 4)))
  have invq : ((q n)^8)⁻¹ ≤ 1 := by
    have hh := inv_anti₀ (by norm_num : (0:ℝ)<1) (show (1:ℝ) ≤ (q n)^8 from one_le_pow₀ hq1)
    simpa only [inv_one] using hh
  have hinv := inv_anti₀ (pow_pos hd 6) (pow_le_pow_left₀ hd.le hxd 6)
  have he := (le_abs_self _).trans (herr n x hax hxq)
  have hle : ((q n)^8)⁻¹*(‖x‖^6)⁻¹ ≤ (d^6)⁻¹ := by
    exact (mul_le_mul_of_nonneg_left hinv (by positivity)).trans (by nlinarith [inv_nonneg.mpr (pow_nonneg hd.le 6)])
  linarith

theorem locallyUniform_of_subsequence
    {X Y : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [UniformSpace Y]
    {U : Set X} (hU : IsOpen U) {f : ℕ → X → Y} {g : X → Y}
    (hc : ∀ n, ContinuousOn (f n) U) (hg : ContinuousOn g U)
    (hsub : ∀ u : ℕ → ℕ, Tendsto u atTop atTop → ∃ v : ℕ → ℕ,
      TendstoLocallyUniformlyOn (fun n => f (u (v n))) g atTop U) :
    TendstoLocallyUniformlyOn f g atTop U := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let F : ℕ → C(U,Y) := fun n => ⟨fun x => f n x, continuousOn_iff_continuous_domRestrict.mp (hc n)⟩
  let G : C(U,Y) := ⟨fun x => g x, continuousOn_iff_continuous_domRestrict.mp hg⟩
  apply tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mpr
  change TendstoLocallyUniformly (fun n x => F n x) G atTop
  apply ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp
  apply tendsto_of_subseq_tendsto
  intro u hu
  obtain ⟨v,hv⟩ := hsub u hu
  refine ⟨v, ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr ?_⟩
  exact tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mp hv

end NeutralAtom
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_Field
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open ContinuousLinearMap
open scoped Topology BigOperators ContDiff Convolution Pointwise ENNReal
namespace NeutralAtom

theorem sommerfeldProfile_continuousOn : ContinuousOn sommerfeldProfile {x | x ≠ 0} := by
  apply continuousOn_const.div (continuous_norm.pow 4).continuousOn
  intro x hx
  exact pow_ne_zero _ (norm_ne_zero_iff.mpr hx)

theorem sommerfeldProfile_density (x : Position) : tfDensityScalar (sommerfeldProfile x) = sommerfeldDensity x := by
  have hn : 0 ≤ ‖x‖ := norm_nonneg x
  have hf : 0 ≤ aTF/‖x‖^4 := div_nonneg aTF_pos.le (pow_nonneg hn 4)
  unfold tfDensityScalar sommerfeldProfile sommerfeldDensity
  rw [max_eq_left hf, Real.div_rpow aTF_pos.le (pow_nonneg hn 4), ← Real.rpow_natCast_mul hn]
  norm_num
  ring

theorem RetainedAnalyticSequence.limit_eq_profile (d : RetainedAnalyticSequence)
    {F : Position → ℝ} (hF : ContinuousOn F {x | x ≠ 0})
    (hu : TendstoLocallyUniformlyOn d.field F atTop {x | x ≠ 0}) :
    ∀ x ≠ 0, F x = sommerfeldProfile x := by
  have herr := expanding_annular_error_locallyUniform d.alim d.qlim d.err
  have hw := screened_semilinear_limit d.σi d.σp d.σb hF hu herr
  have hcap := expanding_annular_cap_limit d.alim d.qlim d.cap hu
  have hL : ∀ a b : ℝ, 0 < a → (∫ x in closedNormAnnulus a b, ‖F x‖) ≤
      2*(d.Ccap/a^4)*(volume (closedNormAnnulus a b)).toReal := by
    intro a b ha
    apply neutral_screened_limit_annular_lone d.Cpos ha d.σi d.σp d.σb d.σmass hF hu
    exact (expanding_annular_cap_eventually (r := b) ha d.alim d.qlim d.cap).mono
      (fun n hn x hx => hn x hx.1 hx.2)
  obtain ⟨K,hK,habs⟩ := semilinear_absolute_bound d.Cpos hF hw hcap hL
  have hpos := screened_limit_positive d.σi d.σp d.σb d.pi d.pp d.pb d.ps d.pm
    d.apos d.alim d.qlim d.aq d.Ucont d.Ulower d.Uupper d.Uweak d.err hu hK.le habs
  have hw' : HasWeakLaplacian F punctured (fun x => 4*Real.pi*kTF*F x^(3/2 : ℝ)) := by
    intro φ hφ hc ht
    rw [hw φ hφ hc ht]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    by_cases hx : x ∈ tsupport φ
    · have hfx : 0 ≤ F x := (div_nonneg d.Bpos.le (pow_nonneg (norm_nonneg x) 4)).trans (hpos x (ht hx))
      simp only [tfReaction, max_eq_left hfx]
    · simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  intro x hx
  have he := weak_sommerfeld_rigidity_exact d.Bpos hF hw' (fun x hx => ⟨hpos x hx, hcap x hx⟩) x hx
  simpa only [sommerfeldProfile, aTF_value] using he

theorem RetainedAnalyticSequence.precompact (d : RetainedAnalyticSequence) :
    ∃ (F : Position → ℝ) (u : ℕ → ℕ), StrictMono u ∧ ContinuousOn F {x | x ≠ 0} ∧
      TendstoLocallyUniformlyOn (fun n => d.field (u n)) F atTop {x | x ≠ 0} := by
  have hb : ∀ a b : ℝ, 0 < a → a < b → ∃ A : ℝ, 0 ≤ A ∧
      ∀ᶠ n in atTop, ∀ x : Position, a ≤ ‖x‖ → ‖x‖ ≤ b →
        screenedField (d.lam n) (d.σ n) x ≤ d.Ccap/‖x‖^4 ∧ d.σ n x ≤ A := by
    intro a b ha _
    exact expanding_annular_density_bound tfDensityScalar_monotone tfDensityScalar_nonneg
      d.Cpos ha d.alim d.qlim d.cap d.err
  obtain ⟨F,u,hu,hF,hconv,_⟩ := neutral_screened_precompact_sequence d.σi d.σp d.σb d.σmass d.Cpos hb
  exact ⟨F,u,hu,hF,hconv⟩

theorem RetainedAnalyticSequence.converges (d : RetainedAnalyticSequence) :
    TendstoLocallyUniformlyOn d.field sommerfeldProfile atTop {x | x ≠ 0} ∧
    TendstoLocallyUniformlyOn d.σ sommerfeldDensity atTop {x | x ≠ 0} := by
  have hu : TendstoLocallyUniformlyOn d.field sommerfeldProfile atTop {x | x ≠ 0} := by
    apply locallyUniform_of_subsequence isOpen_ne
      (fun n => screenedField_continuousOn (d.σi n) (d.σp n) (d.σb n)) sommerfeldProfile_continuousOn
    intro u hu
    let e := d.reindex u hu
    obtain ⟨F,v,hv,hF,hconv⟩ := e.precompact
    have hEq := (e.reindex v hv.tendsto_atTop).limit_eq_profile hF hconv
    refine ⟨v, hconv.congr_right ?_⟩
    exact hEq
  refine ⟨hu, ?_⟩
  have hh := density_locallyUniform_of_vanishing_error hu sommerfeldProfile_continuousOn
    (expanding_annular_error_locallyUniform d.alim d.qlim d.err)
  exact hh.congr_right (fun x _ => sommerfeldProfile_density x)

theorem uniformOn_of_selected_locallyUniformly
    {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    {Θ : ℕ → Type*} {P : ∀ n, Θ n → Prop} {f : ∀ n, Θ n → X → Y}
    {g : X → Y} {U K : Set X} (hK : IsCompact K) (hKU : K ⊆ U)
    (hsel : ∀ u : ℕ → ℕ, StrictMono u → ∀ θ : ∀ n, Θ (u n),
      (∀ n, P (u n) (θ n)) →
      TendstoLocallyUniformlyOn (fun n => f (u n) (θ n)) g atTop U) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ θ, P n θ → ∀ x ∈ K, dist (f n θ x) (g x) < ε := by
  classical
  intro ε hε
  by_contra hh
  have hf := frequently_atTop.mp (not_eventually.mp hh)
  obtain ⟨u,hu,hbad⟩ := Nat.exists_strictMono_subsequence (by
    intro N
    obtain ⟨n,hn,hfail⟩ := hf (N+1)
    exact ⟨n, by omega, hfail⟩)
  have hchoices : ∀ n, ∃ θ : Θ (u n), P (u n) θ ∧
      ∃ x ∈ K, ε ≤ dist (f (u n) θ x) (g x) := by
    intro n
    simpa only [not_forall, Classical.not_imp, not_lt, exists_prop] using hbad n
  choose θ hθ x hx hεx using hchoices
  have ht := hsel u hu θ hθ
  have ht' := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp (ht.mono hKU)
  obtain ⟨n,hn⟩ := ((Metric.tendstoUniformlyOn_iff.mp ht') ε hε).exists
  exact (not_lt_of_ge (hεx n)) (by simpa only [dist_comm] using hn (x n) (hx n))

theorem RetainedAnalyticFamily.uniform {Θ : ℕ → Type*} (d : RetainedAnalyticFamily Θ)
    {K : Set Position} (hK : IsCompact K) (hK0 : (0 : Position) ∉ K) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ θ : Θ n, ∀ x ∈ K,
      |screenedField (d.lam n) (d.σ n θ) x-sommerfeldProfile x| < ε ∧
      |d.σ n θ x-sommerfeldDensity x| < ε := by
  have hKU : K ⊆ {x : Position | x ≠ 0} := fun x hx h => hK0 (h ▸ hx)
  have hfield := uniformOn_of_selected_locallyUniformly (P := fun _ _ => True)
    (f := fun n θ => screenedField (d.lam n) (d.σ n θ)) hK hKU
    (fun u hu θ _ => (d.select u hu.tendsto_atTop θ).converges.1)
  have hdensity := uniformOn_of_selected_locallyUniformly (P := fun _ _ => True)
    (f := d.σ) hK hKU
    (fun u hu θ _ => (d.select u hu.tendsto_atTop θ).converges.2)
  intro ε hε
  filter_upwards [hfield ε hε, hdensity ε hε] with n hn hn' θ x hx
  exact ⟨by simpa only [Real.dist_eq] using hn θ trivial x hx,
    by simpa only [Real.dist_eq] using hn' θ trivial x hx⟩

theorem sommerfeldDensity_continuousOn : ContinuousOn sommerfeldDensity {x | x ≠ 0} := by
  apply continuousOn_const.div (continuous_norm.pow 6).continuousOn
  intro x hx
  exact pow_ne_zero _ (norm_ne_zero_iff.mpr hx)

theorem RetainedAnalyticFamily.uniform_integral {Θ : ℕ → Type*} (d : RetainedAnalyticFamily Θ)
    {S K : Set Position} (hK : IsCompact K) (hK0 : (0 : Position) ∉ K) (hSK : S ⊆ K) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ θ : Θ n,
      |(∫ x in S, d.σ n θ x)-(∫ x in S, sommerfeldDensity x)| < ε := by
  have hKU : K ⊆ {x : Position | x ≠ 0} := fun x hx h => hK0 (h ▸ hx)
  have hi : IntegrableOn sommerfeldDensity S :=
    ((sommerfeldDensity_continuousOn.mono hKU).integrableOn_compact hK).mono_set hSK
  have hSfin : volume S < ⊤ := (measure_mono hSK).trans_lt hK.measure_lt_top
  intro ε hε
  have hV : 0 < volume.real S+1 := by positivity
  have hδ : 0 < ε/(volume.real S+1) := div_pos hε hV
  filter_upwards [d.uniform hK hK0 _ hδ] with n hn θ
  rw [← integral_sub (d.σi n θ).integrableOn hi]
  have hb := norm_setIntegral_le_of_norm_le_const (f := fun x => d.σ n θ x-sommerfeldDensity x)
    (C := ε/(volume.real S+1)) hSfin (fun x hx => by
      simpa only [Real.norm_eq_abs] using (hn θ x (hSK hx)).2.le)
  calc
    _ ≤ (ε/(volume.real S+1))*volume.real S := by simpa only [Real.norm_eq_abs] using hb
    _ < (ε/(volume.real S+1))*(volume.real S+1) :=
      mul_lt_mul_of_pos_left (by linarith) hδ
    _ = ε := div_mul_cancel₀ ε hV.ne'

theorem expectation_tendsto_of_eventual_uniform {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (Y : ∀ n, Ω n → ℝ)
    (G : ∀ n, Set (Ω n)) {C L : ℝ}
    (hY : ∀ n, MemLp (Y n) 2 (μ n)) (hY0 : ∀ n, 0 ≤ᵐ[μ n] Y n)
    (hG : ∀ n, MeasurableSet (G n))
    (hgood : ∀ δ > 0, ∀ᶠ n in atTop, ∀ z ∈ G n, |Y n z-L| < δ)
    (hL2 : ∀ᶠ n in atTop, Real.sqrt (∫ z, Y n z ^ 2 ∂μ n) ≤ C)
    (hbad : Tendsto (fun n => (μ n).real (G n)ᶜ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, Y n z ∂μ n) atTop (𝓝 L) := by
  have hs : Tendsto (fun n => Real.sqrt ((μ n).real (G n)ᶜ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hbad
  have he : Tendsto (fun n => C*Real.sqrt ((μ n).real (G n)ᶜ)+|L| *(μ n).real (G n)ᶜ)
      atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (hs.const_mul C).add (hbad.const_mul |L|)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hε2 : 0 < ε/2 := by positivity
  filter_upwards [hgood (ε/2) hε2, hL2, he.eventually (gt_mem_nhds hε2)] with n hn hL hn'
  rw [Real.dist_eq]
  have hh := expectation_error_bound (hY n) (hY0 n) (hG n) hε2.le
    (fun z hz => (hn z hz).le) hL
  linarith

theorem integrable_sommerfeldDensity_exterior {a : ℝ} (ha : 0 < a) :
    IntegrableOn sommerfeldDensity {x | a < ‖x‖} := by
  change Integrable (fun x : Position => kTF*aTF^(3/2 : ℝ) / ‖x‖^6)
    (volume.restrict {x | a < ‖x‖})
  exact (integrable_exterior_inverse_sixth ha).const_mul (kTF*aTF^(3/2 : ℝ))

theorem sommerfeldDensity_exteriorMass {a : ℝ} (ha : 0 < a) :
    (∫ x : Position in {x | a < ‖x‖}, sommerfeldDensity x) =
      (81*Real.pi^2/2) / a^3 := by
  change (∫ x : Position in {x | a < ‖x‖},
    kTF*aTF^(3/2 : ℝ)*(‖x‖^6)⁻¹) = _
  rw [integral_const_mul, integral_exterior_inverse_sixth ha, profile_coefficient,
    aTF_value]
  field_simp
  ring

theorem sommerfeldDensity_annularMass {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x : Position in {x | a < ‖x‖ ∧ ‖x‖ < b}, sommerfeldDensity x) =
      (81*Real.pi^2/2)/a^3-(81*Real.pi^2/2)/b^3 := by
  rw [← sommerfeldDensity_exteriorMass ha, ← sommerfeldDensity_exteriorMass (ha.trans_le hab),
    ← setIntegral_sdiff (isOpen_lt continuous_const continuous_norm).measurableSet
      (integrable_sommerfeldDensity_exterior ha) (by intro x hx; exact hab.trans_lt hx)]
  symm
  apply setIntegral_congr_set
  have hsphere : ∀ᵐ x : Position, x ∉ Metric.sphere (0 : Position) b := by
    rw [ae_iff]
    convert Measure.addHaar_sphere volume (0 : Position) b using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext x
    simp
  filter_upwards [hsphere] with x hx
  simp only [Metric.mem_sphere, dist_zero_right] at hx
  apply propext
  change (a < ‖x‖ ∧ ¬ b < ‖x‖) ↔ (a < ‖x‖ ∧ ‖x‖ < b)
  constructor
  · rintro ⟨hr,hR⟩
    exact ⟨hr, lt_of_le_of_ne (le_of_not_gt hR) hx⟩
  · exact fun h => ⟨h.1, not_lt_of_ge h.2.le⟩

theorem RetainedAnalyticFamily.expected_integral {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] {G : ∀ n, Set (Ω n)}
    (d : RetainedAnalyticFamily (fun n => G n))
    (σ : ∀ n, Ω n → Position → ℝ)
    (hσ : ∀ n (θ : G n), σ n θ = d.σ n θ)
    {S K : Set Position} (hK : IsCompact K) (hK0 : (0 : Position) ∉ K) (hSK : S ⊆ K)
    (hY : ∀ n, MemLp (fun z => ∫ x in S, σ n z x) 2 (μ n))
    (hY0 : ∀ n, 0 ≤ᵐ[μ n] (fun z => ∫ x in S, σ n z x))
    (hG : ∀ n, MeasurableSet (G n)) {C : ℝ}
    (hL2 : ∀ᶠ n in atTop, Real.sqrt (∫ z, (∫ x in S, σ n z x)^2 ∂μ n) ≤ C)
    (hbad : Tendsto (fun n => (μ n).real (G n)ᶜ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, (∫ x in S, σ n z x) ∂μ n) atTop
      (𝓝 (∫ x in S, sommerfeldDensity x)) := by
  apply expectation_tendsto_of_eventual_uniform μ (fun n z => ∫ x in S, σ n z x) G
    hY hY0 hG ?_ hL2 hbad
  intro ε hε
  filter_upwards [d.uniform_integral hK hK0 hSK ε hε] with n hn z hz
  have hh := hn ⟨z,hz⟩
  simpa only [← hσ n ⟨z,hz⟩] using hh

theorem RetainedAnalyticFamily.expected_annulus {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] {G : ∀ n, Set (Ω n)}
    (d : RetainedAnalyticFamily (fun n => G n))
    (σ : ∀ n, Ω n → Position → ℝ) (hσ : ∀ n (θ : G n), σ n θ = d.σ n θ)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hY : ∀ n, MemLp (fun z => ∫ x in {x | a < ‖x‖ ∧ ‖x‖ < b}, σ n z x) 2 (μ n))
    (hY0 : ∀ n, 0 ≤ᵐ[μ n] (fun z => ∫ x in {x | a < ‖x‖ ∧ ‖x‖ < b}, σ n z x))
    (hG : ∀ n, MeasurableSet (G n)) {C : ℝ}
    (hL2 : ∀ᶠ n in atTop, Real.sqrt (∫ z,
      (∫ x in {x | a < ‖x‖ ∧ ‖x‖ < b}, σ n z x)^2 ∂μ n) ≤ C)
    (hbad : Tendsto (fun n => (μ n).real (G n)ᶜ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, (∫ x in {x | a < ‖x‖ ∧ ‖x‖ < b}, σ n z x) ∂μ n)
      atTop (𝓝 ((81*Real.pi^2/2)/a^3-(81*Real.pi^2/2)/b^3)) := by
  rw [← sommerfeldDensity_annularMass ha hab.le]
  apply d.expected_integral μ σ hσ (isCompact_closedNormAnnulus a b) ?_
    (fun x hx => ⟨hx.1.le,hx.2.le⟩) hY hY0 hG hL2 hbad
  intro hh
  exact (not_le_of_gt ha) (by simpa using hh.1)

end NeutralAtom
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
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_TailClosure
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

lemma atomicTailConstant_nonneg : 0 ≤ atomicTailConstant :=
  (Classical.choose_spec atomic_radial_tail_uniform).1

theorem atomic_radial_tail_bound {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hψ : Antisymmetric ψ) (hm : mass ψ=1)
    {E δ : ℝ} (hE : (E:EReal) ≤ unrestrictedFormBottom S) (hstate : form S ψ ≤ E+δ)
    (hδ : 0 ≤ δ) {h : ℝ} (hh : 0 < h) :
    radialTailPotential ψ h ≤ atomicTailConstant*screenMass δ h/h :=
  (Classical.choose_spec atomic_radial_tail_uniform).2 S hatom ψ hψ hm hE hstate hδ hh

end Coulomb
end

end
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

lemma far_radial_kernel_bound {y z : Space} (hy : y≠0)
    (hfar : 40*atomicCellScale y ≤ ‖z-y‖) (hz : z≠0) :
    coulombKernel (z-y) ≤ 2501*coulombKernel z := by
  have hy0 := atomicCellScale_pos hy
  have hd : 0 < ‖z-y‖ := lt_of_lt_of_le (by positivity : 0 < 40*atomicCellScale y) hfar
  have hz0 := norm_pos_iff.mpr hz
  have hn := norm_add_le (z-y) y
  rw [sub_add_cancel] at hn
  dsimp only [atomicCellScale] at hfar
  have H : (1:ℝ)/‖z-y‖ ≤ 2501/‖z‖ :=
    (div_le_div_iff₀ hd hz0).mpr (by nlinarith)
  simpa only [div_eq_mul_inv,one_mul,coulombKernel] using H

lemma restrictedCore_far_le_inner_tail {n : ℕ} (ψ : H1Vector n)
    {h : ℝ} (hh : 0 < h) {y : Space} (hy : y≠0) :
    restrictedCorePotential ψ {z | 40*atomicCellScale y ≤ ‖z-y‖} y ≤
      restrictedCorePotential ψ (Metric.ball 0 h) y+2501*radialTailPotential ψ h := by
  let A : Set Space := {z | 40*atomicCellScale y ≤ ‖z-y‖}
  have hA : MeasurableSet A := (isClosed_le continuous_const (by fun_prop)).measurableSet
  have hk (z : Space) : (if z∈A then coulombKernel (z-y) else 0) ≤
      (if z∈Metric.ball 0 h then coulombKernel (z-y) else 0)+2501*radialTailKernel h z := by
    have htail := radialTailKernel_nonneg h z
    by_cases hf : z∈A
    · by_cases hi : z∈Metric.ball 0 h
      · simp only [ite_eq_left hf,ite_eq_left hi]; linarith
      · have hz : h ≤ ‖z‖ := by simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hi
        have hz0 : z≠0 := norm_pos_iff.mp (hh.trans_le hz)
        simp only [ite_eq_left hf,ite_eq_right hi,zero_add,radialTailKernel,ite_eq_left hz]
        exact far_radial_kernel_bound hy hf hz0
    · simp only [ite_eq_right hf]
      exact add_nonneg (by split_ifs <;> first | exact inv_nonneg.mpr (norm_nonneg _) | exact le_rfl) (by positivity)
  rw [radialTailPotential_eq]
  change (∑ s : Spins n, ∑ i : Fin n, ∫ x, if position x i∈A then coulombKernel (position x i-y)*‖ψ.value s x‖^2 else 0) ≤ _
  calc
    _ ≤ ∑ s : Spins n, ∑ i : Fin n, ∫ x,
        (if position x i∈Metric.ball 0 h then coulombKernel (position x i-y)*‖ψ.value s x‖^2 else 0)+
        2501*(radialTailKernel h (position x i)*‖ψ.value s x‖^2) := by
      apply Finset.sum_le_sum; intro s hs
      apply Finset.sum_le_sum; intro i hi
      have hiR : Integrable (fun x =>
          (if position x i∈Metric.ball 0 h then coulombKernel (position x i-y)*‖ψ.value s x‖^2 else 0)+
          2501*(radialTailKernel h (position x i)*‖ψ.value s x‖^2)) := by
        exact (restrictedCore_integrable ψ measurableSet_ball s i y).add
          ((radialTailKernel_integrable ψ h s i).const_mul 2501)
      apply integral_mono (restrictedCore_integrable ψ hA s i y) hiR
      intro x
      have H := mul_le_mul_of_nonneg_right (hk (position x i)) (sq_nonneg ‖ψ.value s x‖)
      simpa only [add_mul,ite_mul,zero_mul,mul_assoc] using H
    _ = _ := by
      simp_rw [integral_add (restrictedCore_integrable ψ measurableSet_ball _ _ y)
        ((radialTailKernel_integrable ψ h _ _).const_mul 2501), integral_const_mul]
      simp only [Finset.sum_add_distrib,←Finset.mul_sum,restrictedCorePotential]

theorem atomic_inner_field_bound {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hψ : Antisymmetric ψ) (hm : mass ψ=1)
    {E δ : ℝ} (hE : (E:EReal) ≤ unrestrictedFormBottom S) (hstate : form S ψ ≤ E+δ)
    (hδ : 0 ≤ δ) {h : ℝ} (hh : 0 < h) {y : Space} (hy : y≠0) :
    atomicInnerField S ψ h y ≤
      2*atomicBudgetRecursionC^2*screenFieldUnit δ atomicCountConstant (atomicCellScale y)+
      2501*atomicTailConstant*screenMass δ h/h := by
  have Hb := restrictedCore_far_le_inner_tail ψ hh hy
  have Hr := atomic_expected_raw_field_bound S hatom ψ hψ hm hE hstate hδ hy
  have Ht := atomic_radial_tail_bound S hatom ψ hψ hm hE hstate hδ hh
  dsimp only [atomicInnerField]
  have HM := le_max_left (attraction S y-restrictedCorePotential ψ {z | 40*atomicCellScale y ≤ ‖z-y‖} y) 0
  have Ht' := mul_le_mul_of_nonneg_left Ht (show (0:ℝ) ≤ 2501 by norm_num)
  have he : 2501*(atomicTailConstant*screenMass δ h/h)=2501*atomicTailConstant*screenMass δ h/h := by ring
  rw [he] at Ht'
  linarith

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_NewtonInterior
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

lemma radial_coulomb_lintegral_inner (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    {R : ℝ} (hs : ∀ s, s < R → F s=0) {x : Space} (hxR : ‖x‖ ≤ R) :
    (∫⁻ y : Space, ENNReal.ofReal ‖x-y‖⁻¹*F ‖y‖)=
      ∫⁻ y : Space, ENNReal.ofReal ‖y‖⁻¹*F ‖y‖ := by
  by_cases hx : x=0
  · simp only [hx,zero_sub,norm_neg]
  rw [radial_coulomb_lintegral F hF hx,
    radial_space_lintegral (fun s => ENNReal.ofReal s⁻¹*F s) (by fun_prop)]
  congr 1
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro s hs0
  dsimp only
  by_cases hR : R ≤ s
  · rw [max_eq_right (hxR.trans hR),ENNReal.ofReal_mul (sq_nonneg s),mul_assoc]
  · simp only [hs s (not_le.mp hR),mul_zero]

lemma radial_coulomb_integral_inner {f : Space → ℝ} (hf : Integrable f)
    (hm : Measurable f) (hf0 : ∀ y, 0 ≤ f y) {M : ℝ} (hfM : ∀ y, f y ≤ M)
    (hrad : ∀ y, f y=f (EuclideanSpace.single 0 ‖y‖))
    {R : ℝ} (hfs : ∀ y, ‖y‖ < R → f y=0) {x : Space} (hxR : ‖x‖ ≤ R) :
    (∫ y, coulombKernel (x-y)*f y)=∫ y, coulombKernel y*f y := by
  by_cases hx : x=0
  · simp only [hx,zero_sub,coulombKernel,norm_neg]
  let F : ℝ → ℝ≥0∞ := fun s => if 0 ≤ s then ENNReal.ofReal (f (EuclideanSpace.single 0 s)) else 0
  have hmF : Measurable F := Measurable.ite measurableSet_Ici
    ((hm.comp space_axis_continuous.measurable).ennreal_ofReal) measurable_const
  have he (y : Space) : F ‖y‖=ENNReal.ofReal (f y) := by
    simp only [F,ite_eq_left (norm_nonneg y),←hrad y]
  have hs : ∀ s, s < R → F s=0 := by
    intro s hs
    by_cases hs0 : 0 ≤ s
    · have HH := hfs (EuclideanSpace.single 0 s) (by simpa [Real.norm_eq_abs,abs_of_nonneg hs0] using hs)
      simp only [F,ite_eq_left hs0,HH,ENNReal.ofReal_zero]
    · simp only [F,ite_eq_right hs0]
  have H := radial_coulomb_lintegral_inner F hmF hs hxR
  simp_rw [he] at H
  have hi := coulomb_convolution_integrable hf hm hf0 hfM (by norm_num : (0:ℝ) < 1) x
  have hi0 := coulomb_convolution_integrable hf hm hf0 hfM (by norm_num : (0:ℝ) < 1) 0
  simp only [zero_sub,coulombKernel,norm_neg] at hi0
  change Integrable (fun y => coulombKernel y*f y) at hi0
  have hp (y : Space) : 0 ≤ coulombKernel (x-y)*f y := mul_nonneg (coulombKernel_nonneg _) (hf0 _)
  have hp0 (y : Space) : 0 ≤ coulombKernel y*f y := mul_nonneg (coulombKernel_nonneg _) (hf0 _)
  have hI := ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hp)
  have hI0 := ofReal_integral_eq_lintegral_ofReal hi0 (Eventually.of_forall hp0)
  simp_rw [ENNReal.ofReal_mul (coulombKernel_nonneg _)] at hI hI0
  change ENNReal.ofReal (∫ y, coulombKernel (x-y)*f y)=∫⁻ y, ENNReal.ofReal ‖x-y‖⁻¹*ENNReal.ofReal (f y) at hI
  change ENNReal.ofReal (∫ y, coulombKernel y*f y)=∫⁻ y, ENNReal.ofReal ‖y‖⁻¹*ENNReal.ofReal (f y) at hI0
  rw [←hI,←hI0] at H
  have H' := congrArg ENNReal.toReal H
  simpa only [ENNReal.toReal_ofReal (integral_nonneg hp),ENNReal.toReal_ofReal (integral_nonneg hp0)] using H'

end Coulomb
end

end
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

lemma measurableSet_radialShell (h : ℝ) : MeasurableSet (radialShell h) :=
  measurableSet_ball.diff measurableSet_ball
lemma radialShellDensity_measurable (h : ℝ) : Measurable (radialShellDensity h) :=
  measurable_const.indicator (measurableSet_radialShell h)
lemma radialShellDensity_nonneg (h : ℝ) (z : Space) : 0 ≤ radialShellDensity h z :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) z
lemma radialShellDensity_le (h : ℝ) (z : Space) : radialShellDensity h z ≤ 1 :=
  Set.indicator_le_self' (fun _ _ => zero_le_one) z
lemma radialShellDensity_integrable (h : ℝ) : Integrable (radialShellDensity h) := by
  apply (integrable_indicator_iff (measurableSet_radialShell h)).mpr
  exact integrableOn_const (C:=(1:ℝ)) (measure_ne_top_of_subset sdiff_subset measure_ball_lt_top.ne)

lemma radialShellDensity_mass {h : ℝ} (hh : 0 < h) :
    (∫ z, radialShellDensity h z)=(28*Real.pi/3)*h^3 := by
  unfold radialShellDensity radialShell
  rw [integral_indicator (measurableSet_ball.diff measurableSet_ball),integral_const,measureReal_restrict_apply_univ,smul_eq_mul,mul_one,
    measureReal_sdiff (Metric.ball_subset_ball (by linarith)) measurableSet_ball measure_ball_lt_top.ne,
    volume_real_ball_three (2*h) (by positivity),volume_real_ball_three h hh.le]
  ring

lemma radialShellDensity_radial (h : ℝ) (z : Space) :
    radialShellDensity h z=radialShellDensity h (EuclideanSpace.single 0 ‖z‖) := by
  simp only [radialShellDensity,radialShell,Set.indicator_apply,Set.mem_sdiff,Metric.mem_ball,dist_zero_right,
    PiLp.norm_single,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg z)]

lemma radialShellDensity_zero_inner {h : ℝ} {z : Space} (hz : ‖z‖ < h) :
    radialShellDensity h z=0 := by
  apply Set.indicator_of_notMem
  exact fun hmem => hmem.2 (by simpa only [Metric.mem_ball,dist_zero_right] using hz)

lemma radialShell_coulomb_integrable (h : ℝ) (x : Space) :
    Integrable (fun y => coulombKernel (x-y)*radialShellDensity h y) :=
  coulomb_convolution_integrable (radialShellDensity_integrable h) (radialShellDensity_measurable h)
    (radialShellDensity_nonneg h) (radialShellDensity_le h) (by norm_num : (0:ℝ) < 1) x

lemma radialShellMoment_integrable (h : ℝ) :
    Integrable (fun y => coulombKernel y*radialShellDensity h y) := by
  simpa only [zero_sub,coulombKernel,norm_neg] using radialShell_coulomb_integrable h 0

lemma radialShell_coulomb_inner {h : ℝ} {x : Space} (hx : ‖x‖ ≤ h) :
    (∫ y, coulombKernel (x-y)*radialShellDensity h y)=radialShellMoment h :=
  radial_coulomb_integral_inner (radialShellDensity_integrable h) (radialShellDensity_measurable h)
    (radialShellDensity_nonneg h) (radialShellDensity_le h) (radialShellDensity_radial h)
    (fun _ hz => radialShellDensity_zero_inner hz) hx

lemma radialShellMoment_lower {h : ℝ} (hh : 0 < h) :
    (∫ y, radialShellDensity h y)/(2*h) ≤ radialShellMoment h := by
  rw [div_eq_mul_inv,mul_comm,←integral_const_mul]
  apply integral_mono ((radialShellDensity_integrable h).const_mul _) (radialShellMoment_integrable h)
  intro y
  by_cases hy : y∈radialShell h
  · have hn : ‖y‖ < 2*h := by simpa only [Metric.mem_ball,dist_zero_right] using hy.1
    have hn0 : 0 < ‖y‖ := by
      have H : h ≤ ‖y‖ := by simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hy.2
      exact hh.trans_le H
    exact mul_le_mul_of_nonneg_right ((inv_le_inv₀ (by positivity) hn0).mpr hn.le) (radialShellDensity_nonneg h y)
  · simp only [radialShellDensity,indicator_of_notMem hy,mul_zero,le_refl]

lemma atomicInnerField_shell_average {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) {h : ℝ} (_ : 0 < h) :
    (∫ y, atomicInnerField S ψ h y*radialShellDensity h y)=
      (totalCharge S-expectedPopulation ψ (Metric.ball 0 h))*radialShellMoment h := by
  have hAttr : Integrable (fun y => attraction S y*radialShellDensity h y) := by
    simp_rw [attraction_atomic S hatom,div_eq_mul_inv,mul_assoc]
    exact (radialShellMoment_integrable h).const_mul (totalCharge S)
  have hCore := restrictedCorePotential_mul_integrable ψ (A:=Metric.ball 0 h) measurableSet_ball _ (radialShellDensity_integrable h)
  simp only [atomicInnerField,sub_mul]
  rw [integral_sub hAttr hCore,restrictedCorePotential_fubini ψ measurableSet_ball _ (radialShellDensity_integrable h)]
  have ha : (∫ y, attraction S y*radialShellDensity h y)=totalCharge S*radialShellMoment h := by
    simp_rw [attraction_atomic S hatom,div_eq_mul_inv,mul_assoc]
    exact integral_const_mul _ _
  rw [ha]
  have hc : (∑ s : Spins n, ∑ i : Fin n, ∫ x, if position x i∈Metric.ball 0 h then
      (∫ y, coulombKernel (position x i-y)*radialShellDensity h y)*‖ψ.value s x‖^2 else 0)=
      expectedPopulation ψ (Metric.ball 0 h)*radialShellMoment h := by
    rw [expectedPopulation]
    simp only [Finset.sum_mul,←integral_mul_const]
    apply Finset.sum_congr rfl; intro s hs
    apply Finset.sum_congr rfl; intro i hi
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : position x i∈Metric.ball 0 h
    · have hn : ‖position x i‖ ≤ h := (by simpa only [Metric.mem_ball,dist_zero_right] using hx : ‖position x i‖ < h).le
      rw [ite_eq_left hx,integral_mul_const,radialShell_coulomb_inner hn,indicator_of_mem hx]
      ring
    · simp only [ite_eq_right hx,indicator_of_notMem hx,zero_mul]
  rw [hc]

end Coulomb
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

end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_UpperDeficit
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

lemma atomicInnerFieldConstant_nonneg : 0 ≤ atomicInnerFieldConstant := by
  unfold atomicInnerFieldConstant
  exact add_nonneg (by positivity) (mul_nonneg (by norm_num) atomicTailConstant_nonneg)

lemma atomic_inner_field_shell_bound {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hψ : Antisymmetric ψ) (hm : mass ψ=1)
    {E δ : ℝ} (hE : (E:EReal) ≤ unrestrictedFormBottom S) (hstate : form S ψ ≤ E+δ)
    (hδ : 0 ≤ δ) {h : ℝ} (hh : 0 < h) {y : Space} (hy : y∈radialShell h) :
    atomicInnerField S ψ h y ≤ atomicInnerFieldConstant*screenMass δ h/h := by
  have hlo : h ≤ ‖y‖ := by simpa only [radialShell,Metric.mem_ball,dist_zero_right,not_lt] using hy.2
  have hhi : ‖y‖ ≤ 2*h := (by simpa only [radialShell,Metric.mem_ball,dist_zero_right] using hy.1 : ‖y‖ < 2*h).le
  have hy0 : y≠0 := norm_pos_iff.mp (hh.trans_le hlo)
  have ha := atomicCellScale_pos hy0
  have hlowa : h/100000 ≤ atomicCellScale y := by dsimp only [atomicCellScale]; linarith
  have hhigha : atomicCellScale y ≤ h*100000 := by dsimp only [atomicCellScale]; linarith
  have hc := screenMass_comparable hδ hh (show (1:ℝ) ≤ 100000 by norm_num) hlowa hhigha
  have hm0 := (screenMass_pos δ h).le
  have hunit : screenFieldUnit δ atomicCountConstant (atomicCellScale y) ≤
      Real.sqrt atomicCountConstant*(100000:ℝ)^4*screenMass δ h/h := by
    calc
      _ ≤ (Real.sqrt atomicCountConstant*((100000:ℝ)^3*screenMass δ h))/(atomicCellScale y) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg _)) ha.le
      _ ≤ (Real.sqrt atomicCountConstant*((100000:ℝ)^3*screenMass δ h))/(h/100000) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hlowa
      _ = _ := by field_simp
  have H := atomic_inner_field_bound S hatom ψ hψ hm hE hstate hδ hh hy0
  apply H.trans
  have HH := mul_le_mul_of_nonneg_left hunit (show 0 ≤ 2*atomicBudgetRecursionC^2 by positivity)
  have he : atomicInnerFieldConstant*screenMass δ h/h=
      2*atomicBudgetRecursionC^2*(Real.sqrt atomicCountConstant*(100000:ℝ)^4*screenMass δ h/h)+
      2501*atomicTailConstant*screenMass δ h/h := by unfold atomicInnerFieldConstant; ring
  rw [he]
  exact add_le_add HH le_rfl

theorem atomic_inner_deficit_upper {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hψ : Antisymmetric ψ) (hm : mass ψ=1)
    {E δ : ℝ} (hE : (E:EReal) ≤ unrestrictedFormBottom S) (hstate : form S ψ ≤ E+δ)
    (hδ : 0 ≤ δ) {h : ℝ} (hh : 0 < h) :
    totalCharge S-expectedPopulation ψ (Metric.ball 0 h) ≤
      2*atomicInnerFieldConstant*screenMass δ h := by
  have hm0 := (screenMass_pos δ h).le
  have hR : 0 ≤ 2*atomicInnerFieldConstant*screenMass δ h :=
    mul_nonneg (mul_nonneg (by norm_num) atomicInnerFieldConstant_nonneg) hm0
  by_cases hd : totalCharge S-expectedPopulation ψ (Metric.ball 0 h) ≤ 0
  · exact hd.trans hR
  have hd0 := (not_le.mp hd).le
  have hAttr : Integrable (fun y => attraction S y*radialShellDensity h y) := by
    simp_rw [attraction_atomic S hatom,div_eq_mul_inv,mul_assoc]
    exact (radialShellMoment_integrable h).const_mul (totalCharge S)
  have hCore := restrictedCorePotential_mul_integrable ψ (A:=Metric.ball 0 h) measurableSet_ball _ (radialShellDensity_integrable h)
  have hInt : Integrable (fun y => atomicInnerField S ψ h y*radialShellDensity h y) := by
    convert hAttr.sub hCore using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (ext y; simp only [atomicInnerField,Pi.sub_apply]; ring)
  have hAv : (totalCharge S-expectedPopulation ψ (Metric.ball 0 h))*radialShellMoment h ≤
      (atomicInnerFieldConstant*screenMass δ h/h)*(∫ y,radialShellDensity h y) := by
    rw [←atomicInnerField_shell_average S hatom ψ hh,←integral_const_mul]
    apply integral_mono hInt ((radialShellDensity_integrable h).const_mul _)
    intro y
    by_cases hy : y∈radialShell h
    · exact mul_le_mul_of_nonneg_right (atomic_inner_field_shell_bound S hatom ψ hψ hm hE hstate hδ hh hy)
        (radialShellDensity_nonneg h y)
    · simp only [radialShellDensity,indicator_of_notMem hy,mul_zero,le_refl]
  have hb := radialShellMoment_lower hh
  have hmass : 0 < ∫ y,radialShellDensity h y := by rw [radialShellDensity_mass hh]; positivity
  have hfrac : 0 < (∫ y,radialShellDensity h y)/(2*h) := div_pos hmass (by positivity)
  calc
    _ ≤ ((totalCharge S-expectedPopulation ψ (Metric.ball 0 h))*radialShellMoment h)/
        ((∫ y,radialShellDensity h y)/(2*h)) :=
      (le_div_iff₀ hfrac).mpr (mul_le_mul_of_nonneg_left hb hd0)
    _ ≤ ((atomicInnerFieldConstant*screenMass δ h/h)*(∫ y,radialShellDensity h y))/
        ((∫ y,radialShellDensity h y)/(2*h)) := div_le_div_of_nonneg_right hAv hfrac.le
    _ = _ := by field_simp [hh.ne',hmass.ne']

end Coulomb
end

end
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
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_PhysicalCapMoment
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
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PosteriorSpatialCap
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

lemma physicalSpatialCap_pos : 0<physicalSpatialCap := by
  unfold physicalSpatialCap
  linarith [physicalFieldCapBase_ge_one]

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

theorem measurableSet_spatialAnnulus (a b : ℝ) : MeasurableSet (spatialAnnulus a b) :=
  (isOpen_lt continuous_const continuous_norm).measurableSet.inter
    (isOpen_lt continuous_norm continuous_const).measurableSet

theorem conditional_integral_square_le {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (_hm : m ≤ m₀) {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    (∫ z, μ[X | m] z ^ 2 ∂μ) ≤ ∫ z, X z ^ 2 ∂μ := by
  have hnorm : Integrable (fun z => ‖X z‖ ^ (2 : ℝ)) μ := by
    simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using hX.integrable_sq
  have hJ := integral_norm_condExp_rpow_le (m := m) (by norm_num : (1 : ℝ) ≤ 2) hnorm
  simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using hJ

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_PhysicalInteriorTransfer
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
-- module Solutions.OAIQ062_CR.CoulombRadii_LimitTheory_NeutralCountControl
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
lemma raw_second_expectation_asH1 {n:ℕ} {ψ:Wavefunction n} {g:Gradient n}
    (hd:FormDomain ψ g) {S:Set Position} (hS:MeasurableSet S) :
    rawExpectation ψ (fun x => (rawCount S x)^2)=
      Coulomb.localCountSecondMoment (asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1) S := by
  rw [rawExpectation_eq_stateWeightedIntegral hd.2.2.1 ((measurable_rawCount hS).pow_const 2)
    (C:=(n:ℝ)^2) (fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (rawCount_nonneg S x) (rawCount_le_number S x) 2)]
  change stateWeightedIntegral ψ (fun x => (rawCount S x)^2)=
    Coulomb.potentialForm (fun x => (Coulomb.localCount S x)^2) _
  simpa only [Coulomb.potentialForm,Coulomb.localCount,position_flattenConfiguration,rawCount] using
    (asH1_potentialForm ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1 (fun x => (Coulomb.localCount S x)^2)).symm

lemma physical_exterior_deficit {N:ℕ} {ψ:Wavefunction (N+1)} {g:Gradient (N+1)}
    (hd:FormDomain ψ g) (hn:normSquared ψ=1) (r:ℝ) :
    exteriorMass ψ r=(N+1:ℝ)-Coulomb.expectedPopulation (asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1)
      (Metric.ball 0 r) := by
  rw [←raw_population_asH1 hd measurableSet_ball,integral_rawLaw hd.2.2.1,
    rawExpectation_count_eq_density hd.1 hd.2.2.1 measurableSet_ball]
  have hb : ∫ x in Metric.closedBall (0:Position) r,density ψ x = ∫ x in Metric.ball (0:Position) r,density ψ x := by
    apply setIntegral_congr_set
    have hsphere : ∀ᵐ x : Position,x∉Metric.sphere (0:Position) r := by
      rw [ae_iff]
      convert Measure.addHaar_sphere volume (0:Position) r using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      ext x
      simp
    filter_upwards [hsphere] with x hx
    simp only [Metric.mem_sphere,dist_zero_right] at hx
    apply propext
    constructor
    · intro h
      exact Metric.mem_ball.mpr (lt_of_le_of_ne (Metric.mem_closedBall.mp h) (by simpa using hx))
    · intro h
      exact Metric.mem_closedBall.mpr (Metric.mem_ball.mp h).le
  have H:=integral_add_compl measurableSet_closedBall (integrable_density hd.2.2.1)
    (s:=Metric.closedBall (0:Position) r)
  rw [integral_density hd.2.2.1,hn,mul_one,hb] at H
  have he : (Metric.closedBall (0:Position) r)ᶜ={x:Position | r<‖x‖} := by ext x; simp
  rw [he] at H
  exact eq_sub_of_add_eq' H

 theorem physical_uniform_count_control : UniformGroundStateCountControl := by
  obtain ⟨D,hD,Zmin,H⟩:=physical_neutral_energy_offset
  refine ⟨D,Zmin,hD,?_,?_⟩
  · intro α β hα hαβ
    obtain ⟨C,hC,HC⟩:=Coulomb.atomic_annular_second_moment hα hαβ
    refine ⟨Real.sqrt C,Real.sqrt_nonneg _,?_⟩
    intro N ψ hNZ hψ u hu
    obtain ⟨g,hd,hn,hmin⟩:=hψ
    let v:=asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1
    have hm:Coulomb.mass v=1 := (asH1_mass ..).trans hn
    have hz:1≤N+1:=by omega
    have he:Coulomb.form (Coulomb.atom (N+1) hz) v≤
        (Coulomb.unrestrictedFormBottom (Coulomb.atom (N+1) hz)).toReal+D := by
      rw [asH1_energy]; exact H (N+1) hNZ hz hd hn hmin
    have hE:=Coulomb.atom_unrestricted_bottom_real (N+1) hz v (asH1_antisymmetric hd) hm
    have HH:=HC (Coulomb.atom (N+1) hz) (fun _ => rfl) v (asH1_antisymmetric hd) hm hE.le he hD hu
    rw [raw_second_expectation_asH1 hd (S:={y:Position | α*u<‖y‖ ∧ ‖y‖<β*u}) (measurableSet_lt measurable_const continuous_norm.measurable |>.inter
      (measurableSet_lt continuous_norm.measurable measurable_const))]
    apply (Real.sqrt_le_sqrt HH).trans_eq
    rw [Real.sqrt_mul hC,Real.sqrt_sq (Coulomb.screenMass_pos D u).le]
    rfl
  · refine ⟨2*Coulomb.atomicInnerFieldConstant,mul_nonneg (by norm_num) Coulomb.atomicInnerFieldConstant_nonneg,?_⟩
    intro N ψ hNZ hψ
    obtain ⟨g,hd,hn,hmin⟩:=hψ
    let v:=asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1
    have hm:Coulomb.mass v=1 := (asH1_mass ..).trans hn
    have hz:1≤N+1:=by omega
    have he:Coulomb.form (Coulomb.atom (N+1) hz) v≤
        (Coulomb.unrestrictedFormBottom (Coulomb.atom (N+1) hz)).toReal+D := by
      rw [asH1_energy]; exact H (N+1) hNZ hz hd hn hmin
    have hE:=Coulomb.atom_unrestricted_bottom_real (N+1) hz v (asH1_antisymmetric hd) hm
    have HH:=Coulomb.atomic_inner_deficit_upper (Coulomb.atom (N+1) hz) (fun _ => rfl)
      v (asH1_antisymmetric hd) hm hE.le he hD (by norm_num : (0:ℝ)<1)
    rw [physical_exterior_deficit hd hn]
    simpa [Coulomb.totalCharge,Coulomb.atom,Coulomb.screenMass,Coulomb.screenBaseMass] using HH
end NeutralAtom
end

end
section
noncomputable section
open Filter
open scoped Topology
namespace NeutralAtom

theorem staged_error_tendsto_zero {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    Tendsto (fun n => ((q n : ℝ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hq)

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_PacketBridge
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open ContinuousLinearMap
open scoped Topology BigOperators ContDiff Convolution Pointwise ENNReal
namespace NeutralAtom

theorem packetMass_annulus_localization {n : ℕ} (g : Position → ℝ)
    (hgnorm : (∫ y, g y^2) = 1) (hgsupp : ∀ x, 1 < ‖x‖ → g x = 0)
    {c₁ r₀ s a b : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    (ha : 0 < a) (hab : a < b)
    (hδ : c₁*s^packetExponent < 1/2)
    (hclamp : (1+c₁*s^packetExponent)*r₀ ≤ a*s)
    (x : Configuration n) :
    packetMass g c₁ r₀ s (spatialAnnulus (a*s) (b*s)) x ≤
      rawCount (spatialAnnulus ((a/2)*s) ((2*b)*s)) x := by
  have hdpos : 0 < c₁*s^packetExponent := mul_pos hc (Real.rpow_pos_of_pos hs _)
  have hb : 0 < b := ha.trans hab
  apply packetMass_le_rawCount g hgnorm hc hr hs
  intro z y hy hK
  change a*s < ‖y‖ ∧ ‖y‖ < b*s at hy
  have hz : r₀ ≤ ‖z‖ := by
    by_contra! hz
    have hyc := packetKernel_clamped_support g hgsupp hc hr hs z y hz.le hK
    linarith
  obtain ⟨hl,hu⟩ := packetKernel_relative_support g hgsupp hc hr hs z y hz hK
  change (a/2)*s < ‖z‖ ∧ ‖z‖ < (2*b)*s
  constructor
  · have hn := norm_nonneg z
    have hsmall : (c₁*s^packetExponent)*‖z‖ < ‖z‖ :=
      mul_lt_of_lt_one_left (hr.trans_le hz) (by linarith)
    nlinarith
  · have hlarge : ‖z‖/2 < (1-c₁*s^packetExponent)*‖z‖ := by
      nlinarith [mul_pos (show 0 < 1/2-c₁*s^packetExponent by linarith) (hr.trans_le hz)]
    nlinarith

theorem packet_relative_width_tendsto {s : ℕ → ℝ} (hs : Tendsto s atTop (𝓝 0))
    (c₁ : ℝ) : Tendsto (fun n => c₁*s n^packetExponent) atTop (𝓝 0) := by
  simpa using (hs.rpow_const_nhds_zero (by norm_num [packetExponent])).const_mul c₁

theorem packet_clamp_tendsto {s r₀ : ℕ → ℝ} (hs : Tendsto s atTop (𝓝 0))
    (hr : Tendsto (fun n => r₀ n/s n) atTop (𝓝 0)) (c₁ : ℝ) :
    Tendsto (fun n => ((1+c₁*s n^packetExponent)*r₀ n)/s n) atTop (𝓝 0) := by
  simpa only [mul_zero, add_zero, one_mul, mul_div_assoc] using
    (tendsto_const_nhds.add (packet_relative_width_tendsto hs c₁)).mul hr

theorem eventually_packet_localization {s r₀ : ℕ → ℝ} (N : ℕ → ℕ)
    (g : Position → ℝ) (hgnorm : (∫ y, g y^2) = 1)
    (hgsupp : ∀ x, 1 < ‖x‖ → g x = 0) {c₁ a b : ℝ}
    (hc : 0 < c₁) (ha : 0 < a) (hab : a < b)
    (hsp : ∀ᶠ n in atTop, 0 < s n) (hrp : ∀ᶠ n in atTop, 0 < r₀ n)
    (hs : Tendsto s atTop (𝓝 0))
    (hr : Tendsto (fun n => r₀ n/s n) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ∀ x : Configuration (N n),
      packetMass g c₁ (r₀ n) (s n) (spatialAnnulus (a*s n) (b*s n)) x ≤
        rawCount (spatialAnnulus ((a/2)*s n) ((2*b)*s n)) x := by
  filter_upwards [hsp, hrp,
    (packet_relative_width_tendsto hs c₁).eventually_lt_const (by norm_num : (0:ℝ) < 1/2),
    (packet_clamp_tendsto hs hr c₁).eventually_lt_const ha] with n hsn hrn hδ hcl
  intro x
  exact packetMass_annulus_localization g hgnorm hgsupp hc hrn hsn ha hab hδ
    ((div_lt_iff₀ hsn).mp hcl).le x

theorem rawCount_memLp_measure {n : ℕ} (μ : Measure (Configuration n))
    [IsFiniteMeasure μ] {S : Set Position} (hS : MeasurableSet S) :
    MemLp (rawCount (n := n) S) 2 μ := by
  apply MemLp.of_bound (measurable_rawCount hS).aestronglyMeasurable (n : ℝ)
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (rawCount_nonneg S x)] using rawCount_le_number S x

theorem conditional_mass_l2 {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ m₀) {X Y : Ω → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hX : MemLp X 2 μ) (hX0 : 0 ≤ᵐ[μ] X)
    (hY : AEStronglyMeasurable (m := m₀) Y μ) (hY0 : 0 ≤ᵐ[μ] Y)
    (hYX : Y ≤ᵐ[μ] c • μ[X | m]) :
    MemLp Y 2 μ ∧ Real.sqrt (∫ z, Y z ^ 2 ∂μ) ≤
      c * Real.sqrt (∫ z, X z ^ 2 ∂μ) := by
  have hcond := hX.condExp (m := m) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hcond0 : 0 ≤ᵐ[μ] μ[X | m] := condExp_nonneg hX0
  have hdom : MemLp (c • μ[X | m]) 2 μ := hcond.const_smul c
  have hY2 : MemLp Y 2 μ := hdom.mono' hY (by
    filter_upwards [hY0, hYX] with z hz hzx
    simpa only [Real.norm_eq_abs, abs_of_nonneg hz] using hzx)
  refine ⟨hY2, ?_⟩
  have hsq : (∫ z, Y z ^ 2 ∂μ) ≤ c^2 * (∫ z, X z ^ 2 ∂μ) := by
    calc
      (∫ z, Y z ^ 2 ∂μ) ≤ ∫ z, (c * μ[X | m] z)^2 ∂μ := by
        apply integral_mono_ae hY2.integrable_sq hdom.integrable_sq
        filter_upwards [hY0, hYX, hcond0] with z hz hzx hx
        exact pow_le_pow_left₀ hz hzx 2
      _ = c^2 * (∫ z, μ[X | m] z ^ 2 ∂μ) := by
        simp_rw [mul_pow]
        rw [integral_const_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (conditional_integral_square_le (m₀ := m₀) (m := m) μ hm hX)
        (sq_nonneg c)
  calc
    Real.sqrt (∫ z, Y z ^ 2 ∂μ) ≤ Real.sqrt (c^2 * (∫ z, X z^2 ∂μ)) :=
      Real.sqrt_le_sqrt hsq
    _ = c * Real.sqrt (∫ z, X z^2 ∂μ) := by
      rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

theorem expectation_of_conditional_mass {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ m₀) {X Y : Ω → ℝ} (_hX : Integrable X μ) {c : ℝ}
    (hY : Y =ᵐ[μ] c • μ[X | m]) :
    (∫ z, Y z ∂μ) = c * ∫ z, X z ∂μ := by
  rw [integral_congr_ae hY]
  change (∫ z, c * μ[X | m] z ∂μ) = _
  rw [integral_const_mul, integral_condExp hm]

theorem scaled_count_l2_bound {s D C X Y : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hYX : Y ≤ s^3 * X)
    (hX : X ≤ C*(max (s^3)⁻¹ 1 + Real.sqrt (D*s))) :
    Y ≤ C*(1+Real.sqrt D) := by
  have hs3 : 0 < s^3 := pow_pos hs 3
  have hs3le : s^3 ≤ 1 := pow_le_one₀ hs.le hs1
  have hi : 1 ≤ (s^3)⁻¹ := (one_le_inv₀ hs3).mpr hs3le
  have hsq : Real.sqrt (D*s) ≤ Real.sqrt D :=
    Real.sqrt_le_sqrt (mul_le_of_le_one_right hD hs1)
  have hsm : s^3 * Real.sqrt (D*s) ≤ Real.sqrt D := by
    calc
      s^3 * Real.sqrt (D*s) ≤ 1 * Real.sqrt (D*s) :=
        mul_le_mul_of_nonneg_right hs3le (Real.sqrt_nonneg _)
      _ ≤ _ := by simpa only [one_mul] using hsq
  calc
    Y ≤ s^3 * (C*(max (s^3)⁻¹ 1 + Real.sqrt (D*s))) :=
      hYX.trans (mul_le_mul_of_nonneg_left hX hs3.le)
    _ = C * (1+s^3*Real.sqrt (D*s)) := by
      rw [max_eq_left hi]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl hsm) hC

theorem integral_comp_measurePreserving {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
    {X : Ω → Ξ} (hX : MeasurePreserving X μ ν) {f : Ξ → ℝ}
    (hf : AEStronglyMeasurable f ν) :
    (∫ z, f (X z) ∂μ) = ∫ x, f x ∂ν := by
  rw [← hX.map_eq] at hf ⊢
  exact (integral_map hX.aemeasurable hf).symm

theorem conditional_packet_memLp {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (_hm : m ≤ m₀) {n : ℕ} (ν : Measure (Configuration n)) [IsFiniteMeasure ν]
    (X : Ω → Configuration n) (hX : @MeasurePreserving Ω (Configuration n) m₀ inferInstance X μ ν)
    {g : Position → ℝ} (hg : Continuous g) (hgnorm : (∫ y, g y^2) = 1)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    (S : Set Position) {Y : Ω → ℝ}
    (hY : Y =ᵐ[μ] (s^3) • μ[(fun z => packetMass g c₁ r₀ s S (X z)) | m]) :
    MemLp Y 2 μ := by
  let : MeasurableSpace Ω := m₀
  have hP := (packetMass_memLp hg hgnorm hc hr hs S ν).comp_measurePreserving hX
  exact (memLp_congr_ae hY).mpr
    ((hP.condExp (m := m) (by norm_num : (1 : ℝ≥0∞) ≤ 2)).const_smul (s^3))

theorem conditional_packet_l2_bound {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ m₀) {n : ℕ} (ν : Measure (Configuration n)) [IsFiniteMeasure ν]
    (X : Ω → Configuration n) (hX : @MeasurePreserving Ω (Configuration n) m₀ inferInstance X μ ν)
    {g : Position → ℝ} (hg : Continuous g) (hgnorm : (∫ y, g y^2) = 1)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    (S T : Set Position) (hT : MeasurableSet T)
    (hloc : ∀ x : Configuration n, packetMass g c₁ r₀ s S x ≤ rawCount T x)
    {Y : Ω → ℝ}
    (hY : Y =ᵐ[μ] (s^3) • μ[(fun z => packetMass g c₁ r₀ s S (X z)) | m]) :
    MemLp Y 2 μ ∧ Real.sqrt (∫ z, Y z^2 ∂μ) ≤
      s^3 * Real.sqrt (∫ x, (rawCount T x)^2 ∂ν) := by
  let : MeasurableSpace Ω := m₀
  have hP₀ := packetMass_memLp hg hgnorm hc hr hs S ν
  have hP := hP₀.comp_measurePreserving hX
  have hN₀ := rawCount_memLp_measure ν hT
  have hN := hN₀.comp_measurePreserving hX
  have hY2 := conditional_packet_memLp μ hm ν X hX hg hgnorm hc hr hs S hY
  have hP0 : 0 ≤ᵐ[μ] (fun z => packetMass g c₁ r₀ s S (X z)) :=
    Eventually.of_forall fun z => packetMass_nonneg g hc hr hs S (X z)
  have hY0 : 0 ≤ᵐ[μ] Y := by
    filter_upwards [hY, condExp_nonneg (m := m) hP0] with z hz hpz
    rw [hz]
    exact mul_nonneg (pow_nonneg hs.le 3) hpz
  have hYN : Y ≤ᵐ[μ] (s^3) • μ[(fun z => rawCount T (X z)) | m] := by
    have hh := condExp_mono (m := m) (hP.integrable (by norm_num))
      (hN.integrable (by norm_num)) (Eventually.of_forall (fun z => hloc (X z)))
    filter_upwards [hY,hh] with z hz hhz
    rw [hz]
    exact mul_le_mul_of_nonneg_left hhz (pow_nonneg hs.le 3)
  have hh := conditional_mass_l2 (m₀ := m₀) (m := m) μ hm (pow_nonneg hs.le 3) hN
    (Eventually.of_forall fun z => rawCount_nonneg T (X z)) hY2.aestronglyMeasurable hY0 hYN
  have hi := integral_comp_measurePreserving hX hN₀.integrable_sq.aestronglyMeasurable
  exact ⟨hh.1, by simpa only [Function.comp_apply, hi] using hh.2⟩

theorem expected_conditional_packet {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ m₀) {n : ℕ} (ν : Measure (Configuration n)) [IsFiniteMeasure ν]
    (X : Ω → Configuration n) (hX : @MeasurePreserving Ω (Configuration n) m₀ inferInstance X μ ν)
    {g : Position → ℝ} (hg : Continuous g) (hgnorm : (∫ y, g y^2) = 1)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    (S : Set Position) {Y : Ω → ℝ}
    (hY : Y =ᵐ[μ] (s^3) • μ[(fun z => packetMass g c₁ r₀ s S (X z)) | m]) :
    (∫ z, Y z ∂μ) = s^3 * ∫ x, packetMass g c₁ r₀ s S x ∂ν := by
  let : MeasurableSpace Ω := m₀
  have hP₀ := packetMass_memLp hg hgnorm hc hr hs S ν
  rw [expectation_of_conditional_mass μ hm
    ((hP₀.comp_measurePreserving hX).integrable (by norm_num)) hY]
  simp only [Function.comp_apply]
  rw [integral_comp_measurePreserving hX hP₀.aestronglyMeasurable]

theorem expected_packet_annulus_from_retained {Ω : ℕ → Type*}
    [m₀ : ∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (m : ∀ n, MeasurableSpace (Ω n))
    (hm : ∀ n, m n ≤ m₀ n) (N : ℕ → ℕ)
    (ν : ∀ n, Measure (Configuration (N n))) [∀ n, IsFiniteMeasure (ν n)]
    (X : ∀ n, Ω n → Configuration (N n))
    (hX : ∀ n, @MeasurePreserving (Ω n) (Configuration (N n)) (m₀ n) inferInstance (X n) (μ n) (ν n))
    (s r₀ : ℕ → ℝ) (hsp : ∀ n, 0 < s n) (hrp : ∀ n, 0 < r₀ n)
    (hs : Tendsto s atTop (𝓝 0)) (hr : Tendsto (fun n => r₀ n/s n) atTop (𝓝 0))
    (g : Position → ℝ) (hg : Continuous g) (hgnorm : (∫ y, g y^2) = 1)
    (hgsupp : ∀ x, 1 < ‖x‖ → g x = 0) {c₁ D : ℝ} (hc : 0 < c₁) (hD : 0 ≤ D)
    {G : ∀ n, Set (Ω n)} (hG : ∀ n, MeasurableSet[m₀ n] (G n))
    (hbad : Tendsto (fun n => (μ n).real (G n)ᶜ) atTop (𝓝 0))
    (d : RetainedAnalyticFamily (fun n => G n))
    (σ : ∀ n, Ω n → Position → ℝ) (hσ : ∀ n (θ : G n), σ n θ = d.σ n θ)
    (hcond : ∀ n a b, 0 < a → a < b →
      (fun z => ∫ x in spatialAnnulus a b, σ n z x) =ᵐ[μ n]
        s n^3 • (μ n)[(fun z => packetMass g c₁ (r₀ n) (s n)
          (spatialAnnulus (a*s n) (b*s n)) (X n z)) | m n])
    (hcount : ∀ a b, 0 < a → a < b → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n in atTop, Real.sqrt (∫ x,
        (rawCount (spatialAnnulus (a*s n) (b*s n)) x)^2 ∂ν n) ≤
          C*(max (s n^3)⁻¹ 1 + Real.sqrt (D*s n)))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Tendsto (fun n => s n^3 * ∫ x, packetMass g c₁ (r₀ n) (s n)
      (spatialAnnulus (a*s n) (b*s n)) x ∂ν n)
      atTop (𝓝 ((81*Real.pi^2/2)/a^3-(81*Real.pi^2/2)/b^3)) := by
  let : ∀ n, MeasurableSpace (Ω n) := m₀
  let Y : ∀ n, Ω n → ℝ := fun n z => ∫ x in spatialAnnulus a b, σ n z x
  have hY : ∀ n, MemLp (Y n) 2 (μ n) := fun n =>
    conditional_packet_memLp (μ n) (hm n) (ν n) (X n) (hX n) hg hgnorm hc
      (hrp n) (hsp n) _ (hcond n a b ha hab)
  have hY0 : ∀ n, 0 ≤ᵐ[μ n] Y n := by
    intro n
    have hp : 0 ≤ᵐ[μ n] (fun z => packetMass g c₁ (r₀ n) (s n)
        (spatialAnnulus (a*s n) (b*s n)) (X n z)) := Eventually.of_forall fun z =>
          packetMass_nonneg g hc (hrp n) (hsp n) _ (X n z)
    filter_upwards [hcond n a b ha hab, condExp_nonneg (m := m n) hp] with z hz hpz
    change 0 ≤ Y n z
    change Y n z = _ at hz
    rw [hz]
    exact mul_nonneg (pow_nonneg (hsp n).le 3) hpz
  obtain ⟨C,hC,hcb⟩ := hcount (a/2) (2*b) (by linarith) (by linarith)
  have hL2 : ∀ᶠ n in atTop, Real.sqrt (∫ z, (Y n z)^2 ∂μ n) ≤ C*(1+Real.sqrt D) := by
    filter_upwards [hcb, hs.eventually_lt_const (by norm_num : (0:ℝ) < 1),
      eventually_packet_localization N g hgnorm hgsupp hc ha hab
        (Eventually.of_forall hsp) (Eventually.of_forall hrp) hs hr]
      with n hn hs1 hloc
    have hh := conditional_packet_l2_bound (μ n) (hm n) (ν n) (X n) (hX n)
      hg hgnorm hc (hrp n) (hsp n) _ _ (measurableSet_spatialAnnulus _ _) hloc
      (hcond n a b ha hab)
    exact scaled_count_l2_bound (hsp n) hs1.le hD hC hh.2 hn
  have hh := d.expected_annulus μ σ hσ ha hab hY hY0 hG hL2 hbad
  apply hh.congr'
  filter_upwards [] with n
  exact expected_conditional_packet (μ n) (hm n) (ν n) (X n) (hX n)
    hg hgnorm hc (hrp n) (hsp n) _ (hcond n a b ha hab)

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_Rescaling
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open ContinuousLinearMap
open scoped Topology BigOperators ContDiff Convolution Pointwise ENNReal
namespace NeutralAtom

theorem setIntegral_scaledDensity {D : ℝ} (hD : 0 < D) (σ : Position → ℝ) (S : Set Position) :
    (∫ x in S, scaledDensity D σ x) = D^3*(∫ x in D • S, σ x) := by
  unfold scaledDensity
  rw [integral_const_mul, Measure.setIntegral_comp_smul_of_pos volume σ S hD]
  simp only [Position, finrank_euclideanSpace_fin, smul_eq_mul]
  rw [← mul_assoc]
  congr 1
  field_simp

theorem smul_spatialAnnulus {D : ℝ} (hD : 0 < D) (a b : ℝ) :
    D • spatialAnnulus a b = spatialAnnulus (a*D) (b*D) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hD.ne']
  simp only [spatialAnnulus, Set.mem_ofPred_eq, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hD), ← div_eq_inv_mul]
  constructor
  · rintro ⟨ha,hb⟩
    exact ⟨(lt_div_iff₀ hD).mp ha, (div_lt_iff₀ hD).mp hb⟩
  · rintro ⟨ha,hb⟩
    exact ⟨(lt_div_iff₀ hD).mpr ha, (div_lt_iff₀ hD).mpr hb⟩

theorem annularIntegral_scaledDensity {D : ℝ} (hD : 0 < D) (σ : Position → ℝ) (a b : ℝ) :
    (∫ x in spatialAnnulus a b, scaledDensity D σ x) =
      D^3*(∫ x in spatialAnnulus (a*D) (b*D), σ x) := by
  rw [setIntegral_scaledDensity hD, smul_spatialAnnulus hD]

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_LimitTheory_TailFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal NNReal Classical
noncomputable section
namespace NeutralAtom

theorem quantum_profile_packet_limit_oai
    (N : ℕ → ℕ) (ψ : ∀ n,Wavefunction (N n+1))
    (hψ : ∀ n,IsNormalizedGroundState (N n+1) (ψ n))
    [∀ n,IsProbabilityMeasure (rawLaw (ψ n))]
    {ε B C L M : ℝ} (hε : 0 < ε) (hB : 0 < B) (_ : 0 ≤ M)
    (s : ℕ → ℝ) (hsp : ∀ n,0 < s n) (hs : Tendsto s atTop (𝓝 0))
    (hN : Tendsto (fun n => N n+1) atTop atTop)
    (hr₀ : Tendsto (fun n => initialAtomicRadius ε ((N n+1:ℕ):ℝ)/s n) atTop (𝓝 0))
    (q : ℕ → ℕ) (hq : Tendsto q atTop atTop) (Cq : ℕ → ℝ)
    (d : ∀ n,QuantumProfileDatum (ψ n) ε B C L M (s n) (q n:ℝ) (Cq n))
    (hprob : ∀ n,Cq n*s n^25 ≤ (q n:ℝ)⁻¹)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Tendsto (fun n => s n^3 * ∫ x,packetMass Coulomb.unitWindow 1
      (initialAtomicRadius ε ((N n+1:ℕ):ℝ)) (s n) (spatialAnnulus (a*s n) (b*s n)) x ∂rawLaw (ψ n))
      atTop (𝓝 ((81*Real.pi^2/2)/a^3-(81*Real.pi^2/2)/b^3)) := by
  let Ω := fun n => ObservationSample (N n+1) ((d n).j+1)
  let P := fun n => observationLaw ((d n).j+1) (rawLaw (ψ n))
  let μ := fun n => profileDensity (ψ n) ε (s n) (d n).j
  let rs := fun n (k : Fin ((d n).j+1)) => profileRadius ε (N n) k.val
  let obs := fun n => tailObservation (n:=N n+1) (rs n) (d n).j
  let r := fun n => profileRadius ε (N n) (d n).j
  have hpr (n : ℕ) : 0 < initialAtomicRadius ε ((N n+1:ℕ):ℝ) := initialAtomicRadius_pos hε (by positivity)
  have hr (n : ℕ) : 0 < r n := mul_pos (hpr n) (by positivity)
  have hμi (n : ℕ) (o : Ω n) : Integrable (μ n o) :=
    mixturePacketDensity_integrable Coulomb.unitWindow.continuous Coulomb.unitWindow_mass
      (by norm_num : (0:ℝ)<1) (hpr n) (hsp n) _
  have hμp (n : ℕ) (o : Ω n) (x : Position) : 0 ≤ μ n o x :=
    conditionalPacketDensity_nonneg (P n) Prod.fst (obs n) Coulomb.unitWindow
      (by norm_num : (0:ℝ)<1) (hpr n) (hsp n) _ x
  have hwindow : HasCompactSupport (Coulomb.unitWindow : Position → ℝ) := by
    apply HasCompactSupport.intro (K:=Metric.closedBall 0 1) (isCompact_closedBall _ _)
    intro x hx
    exact Coulomb.unitWindow_support x (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hx)
  have hμb (n : ℕ) : ∃ A : ℝ,∀ o : Ω n,∀ x : Position,μ n o x ≤ A := by
    obtain ⟨A,hA,HA⟩ := conditionalPacketDensity_bounded (P n) Prod.fst (obs n)
      Coulomb.unitWindow.continuous hwindow (by norm_num : (0:ℝ)<1) (hpr n) (hsp n)
    exact ⟨A,fun o => HA (obs n o)⟩
  choose A HA using hμb
  have hmass (n : ℕ) (o : Ω n) : (∫ x,μ n o x)=(N n+1:ℕ) := by
    exact conditionalPacketDensity_mass (P n) Prod.fst (obs n)
      Coulomb.unitWindow.continuous Coulomb.unitWindow_mass (by norm_num : (0:ℝ)<1) (hpr n) (hsp n) (obs n o)
  let f := physical_family_of_data P μ (fun n => N n+1) q s r B C L physicalSpatialCap
    hB physicalSpatialCap_pos.le hsp hr hs hq
    (fun n => by
      apply (le_div_iff₀ (hsp n)).mpr
      simpa only [one_div,mul_comm,div_eq_mul_inv,one_mul] using (d n).low)
    (fun n => (div_le_iff₀ (hsp n)).mpr (by simpa only [div_eq_mul_inv,mul_comm] using (d n).high))
    hμi hμp A HA hmass (fun n => (d n).datum) (fun n => (d n).G)
    (fun n => (d n).valid) (fun n => (d n).band)
  have hbad : Tendsto (fun n => (P n).real (d n).Gᶜ) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => measureReal_nonneg)
      (fun n => (d n).failure.trans (add_le_add le_rfl (hprob n)))
    simpa using ((hs.pow 9).const_mul M).add (staged_error_tendsto_zero hq)
  obtain ⟨D,Z₀,hD,Hcount,_⟩ := physical_uniform_count_control
  apply expected_packet_annulus_from_retained P
    (fun n => MeasurableSpace.comap (obs n) inferInstance)
    (fun n => measurable_iff_comap_le.mp (measurable_tailObservation (rs n) (d n).j))
    (fun n => N n+1) (fun n => rawLaw (ψ n)) (fun _ => Prod.fst)
    (fun n => observationLaw_rawProjection (rawLaw (ψ n))) s
    (fun n => initialAtomicRadius ε ((N n+1:ℕ):ℝ)) hsp hpr hs hr₀
    Coulomb.unitWindow Coulomb.unitWindow.continuous Coulomb.unitWindow_mass Coulomb.unitWindow_support
    (by norm_num : (0:ℝ)<1) hD (fun n => (d n).measurable) hbad f.toAnalytic
    (fun n o => scaledDensity (s n) (μ n o)) (fun _ _ => rfl) ?_ ?_ ha hab
  · intro n a b ha hab
    have HH := conditionalPacketDensity_annulus_eq_condExp (P n) (rawLaw (ψ n))
      (observationLaw_rawProjection (rawLaw (ψ n))) (measurable_tailObservation (rs n) (d n).j)
      Coulomb.unitWindow.continuous Coulomb.unitWindow_mass (by norm_num : (0:ℝ)<1)
      (hpr n) (hsp n) (spatialAnnulus (a*s n) (b*s n))
    filter_upwards [HH] with o ho
    rw [annularIntegral_scaledDensity (hsp n)]
    exact congrArg (fun t => s n^3*t) ho
  · intro a b ha hab
    obtain ⟨K,hK,HK⟩ := Hcount a b ha hab
    refine ⟨K,hK,?_⟩
    filter_upwards [hN.eventually_ge_atTop Z₀] with n hn
    rw [integral_rawLaw (hψ n).choose_spec.1.2.2.1]
    exact HK (N n) (ψ n) hn (hψ n) (s n) (hsp n)
end NeutralAtom
end

end

end OAI
end

theorem solution : type_of% @OAI.NeutralAtom.quantum_profile_packet_limit_oai := @OAI.NeutralAtom.quantum_profile_packet_limit_oai
