-- Prove2me | solution 1 for OAI.NeutralAtom.generalized_outer_radii
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:33:01.673922+00:00
-- url     : https://prove2.me/submissions/85b1e8f4-fa1d-4ce6-831c-77b04e468c26

import Mathlib
import Definitions.Def_CoulombRadii
import Definitions.Def_OAIQ062C008
import Theorems.Thm_OAI_NeutralAtom_physical_initial_event
import Theorems.Thm_OAI_NeutralAtom_physical_neutral_energy_offset
import Theorems.Thm_OAI_NeutralAtom_physical_propagation_good_events
import Theorems.Thm_OAI_NeutralAtom_physical_tf_band
import Theorems.Thm_OAI_NeutralAtom_quantum_profile_packet_limit

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

theorem largeCharge_eq_atTop (m : ℕ) : largeCharge m = atTop := by
  apply inf_eq_left.mpr
  apply Filter.le_principal_iff.mpr
  filter_upwards [eventually_ge_atTop m] with N hN
  omega

theorem bTF_pos : 0 < bTF := by
  unfold bTF
  apply Real.rpow_pos_of_pos
  positivity

theorem density_nonneg {N : ℕ} (ψ : Wavefunction (N + 1)) (x : Position) :
    0 ≤ density ψ x := by
  unfold density
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun σ _ => integral_nonneg fun y => sq_nonneg _

theorem exteriorMass_nonneg {N : ℕ} (ψ : Wavefunction (N + 1)) (r : ℝ) :
    0 ≤ exteriorMass ψ r :=
  integral_nonneg fun x => density_nonneg ψ x

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

theorem exteriorMass_antitone {N : ℕ} {ψ : Wavefunction (N + 1)}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) : Antitone (exteriorMass ψ) := by
  intro r s hrs
  apply setIntegral_mono_set (integrable_density hψ).integrableOn
  · exact Filter.Eventually.of_forall (fun x => density_nonneg ψ x)
  · exact Filter.Eventually.of_forall (fun x hx => lt_of_le_of_lt hrs hx)

theorem radius_bracket {N : ℕ} {ψ : Wavefunction (N + 1)}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) {m : ℕ} {l u : ℝ}
    (hl : (m : ℝ) < exteriorMass ψ l) (hu0 : 0 ≤ u)
    (hu : exteriorMass ψ u ≤ (m : ℝ)) :
    l ≤ radius ψ m ∧ radius ψ m ≤ u := by
  unfold radius
  constructor
  · apply le_csInf (s := {r : ℝ | 0 ≤ r ∧ exteriorMass ψ r ≤ (m : ℝ)}) ⟨u, hu0, hu⟩
    intro r hr
    by_contra! hrl
    have hh := exteriorMass_antitone hψ hrl.le
    exact (not_le_of_gt hl) (hh.trans hr.2)
  · apply csInf_le ⟨0, fun r hr => hr.1⟩
    exact ⟨hu0, hu⟩

theorem scaled_ereal_bounds {c l u : ℝ} {x : EReal} (hc : 0 < c)
    (hl : ((l / c : ℝ) : EReal) ≤ x) (hu : x ≤ ((u / c : ℝ) : EReal)) :
    (l : EReal) ≤ (c : EReal) * x ∧ (c : EReal) * x ≤ (u : EReal) := by
  have hxt : x ≠ ⊤ := ne_of_lt (hu.trans_lt (EReal.coe_lt_top _))
  have hxb : x ≠ ⊥ := ne_of_gt ((EReal.bot_lt_coe _).trans_le hl)
  lift x to ℝ using ⟨hxt, hxb⟩ with x
  rw [← EReal.coe_mul]
  norm_cast at hl hu ⊢
  constructor
  · simpa [mul_comm] using (div_le_iff₀ hc).mp hl
  · simpa [mul_comm] using (le_div_iff₀ hc).mp hu

theorem inner_limits_bracket (Ψ : ∀ N : ℕ, Wavefunction (N + 1))
    {m : ℕ} {c l u : ℝ} (hc : 0 < c)
    (h : ∀ᶠ N in atTop, l ≤ c * radius (Ψ N) m ∧ c * radius (Ψ N) m ≤ u) :
    ((l : EReal) ≤ (c : EReal) * lowerRadius Ψ m ∧
      (c : EReal) * lowerRadius Ψ m ≤ (u : EReal)) ∧
    ((l : EReal) ≤ (c : EReal) * upperRadius Ψ m ∧
      (c : EReal) * upperRadius Ψ m ≤ (u : EReal)) := by
  have hlow : ((l / c : ℝ) : EReal) ≤ lowerRadius Ψ m := by
    unfold lowerRadius
    rw [largeCharge_eq_atTop]
    refine le_liminf_of_le (h := ?_)
    filter_upwards [h] with N hN
    exact EReal.coe_le_coe_iff.mpr ((div_le_iff₀ hc).mpr (by simpa [mul_comm] using hN.1))
  have hupp : upperRadius Ψ m ≤ ((u / c : ℝ) : EReal) := by
    unfold upperRadius
    rw [largeCharge_eq_atTop]
    refine limsup_le_of_le (h := ?_)
    filter_upwards [h] with N hN
    exact EReal.coe_le_coe_iff.mpr ((le_div_iff₀ hc).mpr (by simpa [mul_comm] using hN.2))
  have hlu : lowerRadius Ψ m ≤ upperRadius Ψ m := by
    unfold lowerRadius upperRadius
    rw [largeCharge_eq_atTop]
    exact liminf_le_limsup
  exact ⟨scaled_ereal_bounds hc hlow (hlu.trans hupp),
    scaled_ereal_bounds hc (hlow.trans hlu) hupp⟩

theorem tendsto_ereal_of_eventual_brackets {α : Type*} {f : Filter α}
    {v : α → EReal} {b : ℝ} (hb : 0 < b)
    (h : ∀ l u : ℝ, 0 < l → l < b → b < u →
      ∀ᶠ a in f, (l : EReal) ≤ v a ∧ v a ≤ (u : EReal)) :
    Tendsto v f (𝓝 (b : EReal)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨l, hal, hlb⟩ := EReal.exists_between_coe_real ha
    have hmax : max l (b / 2) < b := max_lt (EReal.coe_lt_coe_iff.mp hlb) (by linarith)
    have hpos : 0 < max l (b / 2) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    filter_upwards [h (max l (b / 2)) (b + 1) hpos hmax (by linarith)] with i hi
    exact (hal.trans_le (EReal.coe_le_coe_iff.mpr (le_max_left _ _))).trans_le hi.1
  · intro a ha
    obtain ⟨u, hbu, hua⟩ := EReal.exists_between_coe_real ha
    filter_upwards [h (b / 2) u (by linarith) (by linarith)
      (EReal.coe_lt_coe_iff.mp hbu)] with i hi
    exact hi.2.trans_lt hua

theorem iterated_limits_of_radius_brackets (Ψ : ∀ N : ℕ, Wavefunction (N + 1))
    (h : ∀ l u : ℝ, 0 < l → l < bTF → bTF < u →
      ∀ᶠ m : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        l ≤ (m : ℝ) ^ (1 / 3 : ℝ) * radius (Ψ N) m ∧
        (m : ℝ) ^ (1 / 3 : ℝ) * radius (Ψ N) m ≤ u) :
    Tendsto (fun m : ℕ => (((m : ℝ) ^ (1 / 3 : ℝ) : ℝ) : EReal) * upperRadius Ψ m)
      atTop (𝓝 (bTF : EReal)) ∧
    Tendsto (fun m : ℕ => (((m : ℝ) ^ (1 / 3 : ℝ) : ℝ) : EReal) * lowerRadius Ψ m)
      atTop (𝓝 (bTF : EReal)) := by
  have hb : ∀ l u : ℝ, 0 < l → l < bTF → bTF < u →
      ∀ᶠ m : ℕ in atTop,
        (((l : EReal) ≤ ((m : ℝ) ^ (1 / 3 : ℝ) : ℝ) * lowerRadius Ψ m ∧
        ((m : ℝ) ^ (1 / 3 : ℝ) : ℝ) * lowerRadius Ψ m ≤ (u : EReal)) ∧
        ((l : EReal) ≤ ((m : ℝ) ^ (1 / 3 : ℝ) : ℝ) * upperRadius Ψ m ∧
        ((m : ℝ) ^ (1 / 3 : ℝ) : ℝ) * upperRadius Ψ m ≤ (u : EReal))) := by
    intro l u hl hlb hbu
    filter_upwards [h l u hl hlb hbu, eventually_gt_atTop (0 : ℕ)] with m hm hp
    apply inner_limits_bracket Ψ (Real.rpow_pos_of_pos (by exact_mod_cast hp) _) hm
  constructor
  · apply tendsto_ereal_of_eventual_brackets bTF_pos
    intro l u hl hlb hbu
    exact (hb l u hl hlb hbu).mono fun _ hi => hi.2
  · apply tendsto_ereal_of_eventual_brackets bTF_pos
    intro l u hl hlb hbu
    exact (hb l u hl hlb hbu).mono fun _ hi => hi.1

theorem uniform_threshold_of_sequential {X : ℕ → Type*}
    (P : ∀ N, X N → Prop) (Zmin : ℕ → ℕ) (f : ℕ → ∀ N : ℕ, X N → ℝ) (c : ℝ)
    (hseq : ∀ (m Z : ℕ → ℕ), StrictMono m → (∀ n, Zmin (m n) ≤ Z n) →
      ∀ x : ∀ n, X (Z n), (∀ n, P (Z n) (x n)) →
      Tendsto (fun n => f (m n) (Z n) (x n)) atTop (𝓝 c)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      ∀ N, Zmin m ≤ N → ∀ x : X N, P N x → |f m N x - c| < ε := by
  classical
  intro ε hε
  by_contra hnot
  have hbad := frequently_atTop.mp (not_eventually.mp hnot)
  obtain ⟨m, hm, hfail⟩ := Nat.exists_strictMono_subsequence (by
    intro M
    obtain ⟨n, hn, hbadn⟩ := hbad (M + 1)
    exact ⟨n, by omega, hbadn⟩)
  have hchoose : ∀ n, ∃ N, Zmin (m n) ≤ N ∧
      ∃ x : X N, P N x ∧ ε ≤ |f (m n) N x - c| := by
    intro n
    simpa only [not_forall, Classical.not_imp, not_lt, exists_prop] using hfail n
  choose Z hZ x hx hεx using hchoose
  have ht := hseq m Z hm hZ x hx
  obtain ⟨n, hn⟩ := ((Metric.tendsto_nhds.mp ht) ε hε).exists
  exact (not_lt_of_ge (hεx n)) (by simpa only [Real.dist_eq] using hn)

theorem cube_root_cube (m : ℕ) : ((m : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = m := by
  simpa only [one_div, Nat.cast_ofNat] using
    Real.rpow_inv_natCast_pow (x := (m : ℝ)) (n := 3) (by positivity) (by decide)

theorem bTF_cube : bTF ^ (3 : ℕ) = 81 * Real.pi ^ 2 / 2 := by
  unfold bTF
  simpa only [one_div, Nat.cast_ofNat] using
    Real.rpow_inv_natCast_pow (x := 81 * Real.pi ^ 2 / 2) (n := 3)
      (by positivity) (by decide)

theorem normalized_tail_scale (m : ℕ) (T : ℝ → ℝ) (a : ℝ) :
    ((m : ℝ) ^ (-(1 / 3 : ℝ))) ^ (3 : ℕ) * T (a * (m : ℝ) ^ (-(1 / 3 : ℝ))) =
      T (a / (m : ℝ) ^ (1 / 3 : ℝ)) / m := by
  rw [Real.rpow_neg (by positivity), inv_pow, cube_root_cube]
  simp only [div_eq_mul_inv, mul_comm]

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

theorem measurableSet_spatialAnnulus (a b : ℝ) : MeasurableSet (spatialAnnulus a b) :=
  (isOpen_lt continuous_const continuous_norm).measurableSet.inter
    (isOpen_lt continuous_norm continuous_const).measurableSet

theorem packetMass_annulus_sandwich {n : ℕ} (g : Position → ℝ)
    (hgnorm : (∫ y, g y ^ 2) = 1) (hgsupp : ∀ x, 1 < ‖x‖ → g x = 0)
    {c₁ r₀ s a b η : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    (ha : 0 < a) (hab : a < b) (hη : 0 < η) (hηa : η < a)
    (hδ : (c₁ * s ^ packetExponent) * b < η)
    (hclamp : (1 + c₁ * s ^ packetExponent) * r₀ ≤ (a-η)*s)
    (x : Configuration n) :
    packetMass g c₁ r₀ s (spatialAnnulus ((a+η)*s) ((b-η)*s)) x ≤
      rawCount (spatialAnnulus (a*s) (b*s)) x ∧
    rawCount (spatialAnnulus (a*s) (b*s)) x ≤
      packetMass g c₁ r₀ s (spatialAnnulus ((a-η)*s) ((b+η)*s)) x := by
  have hdpos : 0 < c₁ * s ^ packetExponent := mul_pos hc (Real.rpow_pos_of_pos hs _)
  have hdb : 0 < b := ha.trans hab
  have hd1 : c₁ * s ^ packetExponent < 1 := by nlinarith
  have hr_as : r₀ < a*s := by nlinarith
  constructor
  · apply packetMass_le_rawCount g hgnorm hc hr hs
    intro z y hy hK
    change (a+η)*s < ‖y‖ ∧ ‖y‖ < (b-η)*s at hy
    have hz : r₀ ≤ ‖z‖ := by
      by_contra! hz
      have hyc := packetKernel_clamped_support g hgsupp hc hr hs z y hz.le hK
      nlinarith
    obtain ⟨hl, hu⟩ := packetKernel_relative_support g hgsupp hc hr hs z y hz hK
    change a*s < ‖z‖ ∧ ‖z‖ < b*s
    constructor
    · by_contra! hn
      have hstep : (1+c₁*s^packetExponent)*‖z‖ ≤ (1+c₁*s^packetExponent)*(a*s) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
      have hδa : (c₁*s^packetExponent)*a < η := by nlinarith
      have hsmall := mul_lt_mul_of_pos_right hδa hs
      nlinarith
    · by_contra! hn
      have hstep : (1-c₁*s^packetExponent)*(b*s) ≤ (1-c₁*s^packetExponent)*‖z‖ :=
        mul_le_mul_of_nonneg_left hn (by linarith)
      have hsmall := mul_lt_mul_of_pos_right hδ hs
      nlinarith
  · apply rawCount_le_packetMass g hgnorm hc hr hs
    intro z y hz hK
    change a*s < ‖z‖ ∧ ‖z‖ < b*s at hz
    obtain ⟨hl, hu⟩ := packetKernel_relative_support g hgsupp hc hr hs z y
      (hr_as.le.trans hz.1.le) hK
    have hsmall := mul_lt_mul_of_pos_right hδ hs
    have hstep : (c₁*s^packetExponent)*‖z‖ < (c₁*s^packetExponent)*(b*s) :=
      mul_lt_mul_of_pos_left hz.2 hdpos
    change (a-η)*s < ‖y‖ ∧ ‖y‖ < (b+η)*s
    constructor <;> nlinarith

theorem exteriorMass_sub {N : ℕ} {ψ : Wavefunction (N+1)}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) {r R : ℝ} (hrR : r ≤ R) :
    exteriorMass ψ r - exteriorMass ψ R = ∫ x in spatialAnnulus r R, density ψ x := by
  unfold exteriorMass
  rw [← setIntegral_sdiff (isOpen_lt continuous_const continuous_norm).measurableSet
    (integrable_density hψ).integrableOn (by intro x hx; exact lt_of_le_of_lt hrR hx)]
  apply setIntegral_congr_set
  have hsphere : ∀ᵐ x : Position, x ∉ Metric.sphere (0 : Position) R := by
    rw [ae_iff]
    convert Measure.addHaar_sphere volume (0 : Position) R using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext x
    simp
  filter_upwards [hsphere] with x hx
  simp only [Metric.mem_sphere, dist_zero_right] at hx
  apply propext
  change (r < ‖x‖ ∧ ¬ R < ‖x‖) ↔ (r < ‖x‖ ∧ ‖x‖ < R)
  constructor
  · rintro ⟨hr, hR⟩
    exact ⟨hr, lt_of_le_of_ne (le_of_not_gt hR) hx⟩
  · exact fun h => ⟨h.1, not_lt_of_ge h.2.le⟩

theorem dyadic_tail_bound {T : ℝ → ℝ} {A B : ℝ} (hA : 0 ≤ A)
    (hT : Antitone T) (hB : T 1 ≤ B)
    (hshell : ∀ r : ℝ, 0 < r → r < 1 → T r - T (2*r) ≤ A / r^3)
    {r : ℝ} (hr : 0 < r) : T r ≤ ((8/7 : ℝ)*A) / r^3 + B := by
  have hind : ∀ n : ℕ, ∀ u : ℝ, 0 < u → 1 ≤ (2:ℝ)^n*u →
      T u ≤ ((8/7 : ℝ)*A) / u^3 + B := by
    intro n
    induction n with
    | zero =>
      intro u hu htop
      have ht : T u ≤ B := (hT (by simpa using htop)).trans hB
      have : 0 ≤ ((8/7 : ℝ)*A) / u^3 := by positivity
      linarith
    | succ n ih =>
      intro u hu htop
      by_cases hu1 : 1 ≤ u
      · have ht := (hT hu1).trans hB
        have : 0 ≤ ((8/7 : ℝ)*A) / u^3 := by positivity
        linarith
      · have htop' : 1 ≤ (2:ℝ)^n*(2*u) := by
          simpa only [pow_succ, mul_assoc] using htop
        have hnext := ih (2*u) (by positivity) htop'
        have hnow := hshell u hu (lt_of_not_ge hu1)
        have hid : A/u^3 + ((8/7:ℝ)*A)/(2*u)^3 = ((8/7:ℝ)*A)/u^3 := by
          field_simp
          ring
        linarith
  obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).eventually
    (eventually_ge_atTop (1/r))).exists
  exact hind n r hr ((div_le_iff₀ hr).mp hn)

theorem radius_scales_admissible (Zbar : ℝ → ℕ) (m N : ℕ → ℕ)
    (hm : StrictMono m) (hN : ∀ n, radiusChargeThreshold Zbar (m n) ≤ N n) :
    Admissible Zbar (fun n => (m n : ℝ)^(-(1/3 : ℝ))) N := by
  have hmR : Tendsto (fun n => (m n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hm.tendsto_atTop
  have hmp : ∀ᶠ n in atTop, 0 < (m n : ℝ) := hmR.eventually (eventually_gt_atTop 0)
  refine ⟨hmp.mono (fun n hn => Real.rpow_pos_of_pos hn _),
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/3)).comp hmR, ?_, ?_⟩
  · exact Eventually.of_forall fun n =>
      ((le_max_left _ _).trans (hN n)).trans (Nat.le_succ _)
  · apply tendsto_atTop_mono' atTop _ hmR
    filter_upwards [hmp] with n hn
    rw [Real.rpow_neg hn.le, inv_pow, cube_root_cube, ← div_eq_mul_inv]
    apply (le_div_iff₀ hn).mpr
    have hlarge : ((m n + 1 : ℕ) : ℝ)^2 ≤ (N n : ℝ) := by
      exact_mod_cast ((le_max_right _ _).trans (hN n))
    simp only [Nat.cast_add, Nat.cast_one] at hlarge
    nlinarith

theorem iterated_limits_of_expected_exterior_asymptotic (Zbar : ℝ → ℕ)
    (htail : ExpectedExteriorAsymptotic Zbar)
    (Ψ : ∀ N : ℕ, Wavefunction (N + 1))
    (hΨ : ∀ N, IsNormalizedGroundState (N+1) (Ψ N)) :
    Tendsto (fun m : ℕ => (((m : ℝ) ^ (1 / 3 : ℝ) : ℝ) : EReal) * upperRadius Ψ m)
      atTop (𝓝 (bTF : EReal)) ∧
    Tendsto (fun m : ℕ => (((m : ℝ) ^ (1 / 3 : ℝ) : ℝ) : EReal) * lowerRadius Ψ m)
      atTop (𝓝 (bTF : EReal)) := by
  have huniform : ∀ a : ℝ, 0 < a → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ m : ℕ in atTop, ∀ N, radiusChargeThreshold Zbar m ≤ N →
      ∀ ψ : Wavefunction (N+1), IsNormalizedGroundState (N+1) ψ →
        |exteriorMass ψ (a / (m : ℝ)^(1/3 : ℝ)) / m - bTF^ (3 : ℕ) / a^ (3 : ℕ)| < ε := by
    intro a ha
    apply uniform_threshold_of_sequential
      (fun N ψ => IsNormalizedGroundState (N+1) ψ)
      (radiusChargeThreshold Zbar)
      (fun m N ψ => exteriorMass ψ (a / (m : ℝ)^(1/3 : ℝ)) / m)
      (bTF^ (3 : ℕ) / a^ (3 : ℕ))
    intro m N hm hN ψ hψ
    have ht := htail _ _ (radius_scales_admissible Zbar m N hm hN) ψ hψ a ha
    simpa only [normalized_tail_scale] using ht
  apply iterated_limits_of_radius_brackets Ψ
  intro l u hl hlb hbu
  have hu : 0 < u := bTF_pos.trans hbu
  have cl : 1 < bTF^ (3 : ℕ) / l^ (3 : ℕ) :=
    (one_lt_div₀ (pow_pos hl 3)).mpr (pow_lt_pow_left₀ hlb hl.le (by decide))
  have cu : bTF^ (3 : ℕ) / u^ (3 : ℕ) < 1 :=
    (div_lt_one (pow_pos hu 3)).mpr (pow_lt_pow_left₀ hbu bTF_pos.le (by decide))
  filter_upwards [huniform l hl ((bTF^ (3 : ℕ) / l^ (3 : ℕ) - 1)/2) (by linarith),
    huniform u hu ((1 - bTF^ (3 : ℕ) / u^ (3 : ℕ))/2) (by linarith),
    eventually_gt_atTop (0 : ℕ)] with m hml hmu hm
  filter_upwards [eventually_ge_atTop (radiusChargeThreshold Zbar m)] with N hN
  have hmp : 0 < (m : ℝ) := by exact_mod_cast hm
  have hc : 0 < (m : ℝ)^(1/3 : ℝ) := Real.rpow_pos_of_pos hmp _
  have hL := (abs_lt.mp (hml N hN (Ψ N) (hΨ N))).1
  have hU := (abs_lt.mp (hmu N hN (Ψ N) (hΨ N))).2
  have hL' : (m : ℝ) < exteriorMass (Ψ N) (l / (m : ℝ)^(1/3 : ℝ)) :=
    (one_lt_div₀ hmp).mp (by linarith)
  have hU' : exteriorMass (Ψ N) (u / (m : ℝ)^(1/3 : ℝ)) < (m : ℝ) :=
    (div_lt_one hmp).mp (by linarith)
  obtain ⟨g, hdom, _, _⟩ := hΨ N
  obtain ⟨hlo, hup⟩ := radius_bracket hdom.2.2.1 hL' (by positivity) hU'.le
  exact ⟨by simpa [mul_comm] using (div_le_iff₀ hc).mp hlo,
    by simpa [mul_comm] using (le_div_iff₀ hc).mp hup⟩

theorem rawExpectation_count_le_l2 {N : ℕ} {ψ : Wavefunction (N+1)}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hn : normSquared ψ = 1)
    {S : Set Position} (hS : MeasurableSet S) :
    rawExpectation ψ (rawCount S) ≤
      Real.sqrt (rawExpectation ψ (fun x => (rawCount S x)^2)) := by
  have := rawLaw_isProbability hψ hn
  have h := exceptional_event_bound (rawCount_memLp hψ hn hS)
    (Eventually.of_forall (rawCount_nonneg S)) MeasurableSet.univ
  simpa only [setIntegral_univ, probReal_univ, Real.sqrt_one, mul_one,
    integral_rawLaw hψ] using h

theorem small_shell_bounds_of_count_control (hcount : UniformGroundStateCountControl) :
    ∃ (A B : ℝ) (Z₀ : ℕ), 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (N : ℕ) (ψ : Wavefunction (N+1)), Z₀ ≤ N+1 →
      IsNormalizedGroundState (N+1) ψ →
      exteriorMass ψ 1 ≤ B ∧ ∀ r : ℝ, 0 < r → r < 1 →
        exteriorMass ψ r - exteriorMass ψ (2*r) ≤ A/r^3 := by
  obtain ⟨D, Z₀, hD, hann, C₀, hC₀, h₀⟩ := hcount
  obtain ⟨C, hC, hCbound⟩ := hann 1 2 (by norm_num) (by norm_num)
  refine ⟨C*(1+Real.sqrt D), C₀*(1+Real.sqrt D), Z₀, by positivity, by positivity, ?_⟩
  intro N ψ hZ hψ
  refine ⟨h₀ N ψ hZ hψ, ?_⟩
  intro r hr hr1
  obtain ⟨g, hdom, hnorm, _⟩ := hψ
  have hbound := hCbound N ψ hZ ⟨g, hdom, hnorm, by assumption⟩ r hr
  have hmean := rawExpectation_count_le_l2 hdom.2.2.1 hnorm
    (measurableSet_spatialAnnulus (a := r) (b := 2*r))
  have hmean' : exteriorMass ψ r - exteriorMass ψ (2*r) ≤
      C * (max (r^3)⁻¹ 1 + Real.sqrt (D*r)) := by
    rw [exteriorMass_sub hdom.2.2.1 (by linarith),
      ← rawExpectation_count_eq_density hdom.1 hdom.2.2.1 (measurableSet_spatialAnnulus _ _)]
    exact hmean.trans (by simpa only [one_mul, spatialAnnulus] using hbound)
  have hr3 : 0 < r^3 := by positivity
  have hr3le : r^3 ≤ 1 := pow_le_one₀ hr.le hr1.le
  have hinv : 1 ≤ (r^3)⁻¹ := (one_le_inv₀ hr3).mpr hr3le
  have hsqrt : Real.sqrt (D*r) ≤ Real.sqrt D :=
    Real.sqrt_le_sqrt (mul_le_of_le_one_right hD hr1.le)
  calc
    exteriorMass ψ r - exteriorMass ψ (2*r) ≤
        C*((r^3)⁻¹ + Real.sqrt D) := by
      apply hmean'.trans
      rw [max_eq_left hinv]
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hsqrt) hC
    _ ≤ C*((r^3)⁻¹ + Real.sqrt D*(r^3)⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact add_le_add le_rfl (le_mul_of_one_le_right (Real.sqrt_nonneg D) hinv)
    _ = (C*(1+Real.sqrt D))/r^3 := by ring

theorem scaled_dyadic_tail_bound {T : ℝ → ℝ} {A B s M : ℝ} (hA : 0 ≤ A)
    (hT : Antitone T) (hB : T 1 ≤ B)
    (hshell : ∀ r : ℝ, 0 < r → r < 1 → T r - T (2*r) ≤ A/r^3)
    (hs : 0 < s) (hM : 0 < M) :
    s^3*T (M*s) ≤ ((8/7 : ℝ)*A)/M^3 + B*s^3 := by
  have h := mul_le_mul_of_nonneg_left
    (dyadic_tail_bound hA hT hB hshell (mul_pos hM hs)) (pow_nonneg hs.le 3)
  calc
    s^3*T (M*s) ≤ s^3*(((8/7:ℝ)*A)/(M*s)^3+B) := h
    _ = _ := by field_simp

theorem tails_converge_of_annuli {T : ℕ → ℝ → ℝ} {β : ℕ → ℝ} {C D a : ℝ}
    (hC : 0 ≤ C) (ha : 0 < a) (hβ : Tendsto β atTop (𝓝 0))
    (hT : ∀ n r, 0 ≤ T n r)
    (hbound : ∀ M : ℝ, 0 < M → ∀ᶠ n in atTop, T n M ≤ D/M^3 + β n)
    (hann : ∀ M : ℝ, a < M →
      Tendsto (fun n => T n a - T n M) atTop (𝓝 (C/a^3-C/M^3))) :
    Tendsto (fun n => T n a) atTop (𝓝 (C/a^3)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsmall : Tendsto (fun M : ℝ => (C+D)/M^3) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by decide : 3 ≠ 0))
  obtain ⟨M, hlarge, hMsmall⟩ := ((eventually_gt_atTop a).and
    (hsmall.eventually (gt_mem_nhds (by linarith : (0:ℝ)<ε/3)))).exists
  have hM : 0 < M := ha.trans hlarge
  have hann' := (Metric.tendsto_nhds.mp (hann M hlarge)) (ε/3) (by positivity)
  have hβ' := hβ.eventually (gt_mem_nhds (by linarith : (0:ℝ)<ε/3))
  filter_upwards [hann', hβ', hbound M hM] with n hn hβn hbn
  rw [Real.dist_eq] at hn ⊢
  have hsplit : |T n a - C/a^3| ≤
      |(T n a-T n M)-(C/a^3-C/M^3)| + T n M + C/M^3 := by
    have hh := abs_add_le ((T n a-T n M)-(C/a^3-C/M^3)) (T n M-C/M^3)
    have hh' := abs_sub (T n M) (C/M^3)
    rw [abs_of_nonneg (hT n M), abs_of_nonneg (div_nonneg hC (pow_nonneg hM.le 3))] at hh'
    have hid : ((T n a-T n M)-(C/a^3-C/M^3)) + (T n M-C/M^3) =
        T n a-C/a^3 := by ring
    rw [hid] at hh
    linarith
  have hcoeff : C/M^3+D/M^3 = (C+D)/M^3 := by ring
  linarith

end NeutralAtom
end

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

theorem packet_relative_width_tendsto {s : ℕ → ℝ} (hs : Tendsto s atTop (𝓝 0))
    (c₁ : ℝ) : Tendsto (fun n => c₁*s n^packetExponent) atTop (𝓝 0) := by
  simpa using (hs.rpow_const_nhds_zero (by norm_num [packetExponent])).const_mul c₁

theorem packet_clamp_tendsto {s r₀ : ℕ → ℝ} (hs : Tendsto s atTop (𝓝 0))
    (hr : Tendsto (fun n => r₀ n/s n) atTop (𝓝 0)) (c₁ : ℝ) :
    Tendsto (fun n => ((1+c₁*s n^packetExponent)*r₀ n)/s n) atTop (𝓝 0) := by
  simpa only [mul_zero, add_zero, one_mul, mul_div_assoc] using
    (tendsto_const_nhds.add (packet_relative_width_tendsto hs c₁)).mul hr

theorem eventually_packet_sandwich {s r₀ : ℕ → ℝ} (N : ℕ → ℕ)
    (g : Position → ℝ) (hgnorm : (∫ y, g y^2) = 1)
    (hgsupp : ∀ x, 1 < ‖x‖ → g x = 0) {c₁ a b η : ℝ}
    (hc : 0 < c₁) (ha : 0 < a) (hab : a < b) (hη : 0 < η) (hηa : η < a)
    (hsp : ∀ᶠ n in atTop, 0 < s n) (hrp : ∀ᶠ n in atTop, 0 < r₀ n)
    (hs : Tendsto s atTop (𝓝 0))
    (hr : Tendsto (fun n => r₀ n/s n) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ∀ x : Configuration (N n),
      packetMass g c₁ (r₀ n) (s n) (spatialAnnulus ((a+η)*s n) ((b-η)*s n)) x ≤
        rawCount (spatialAnnulus (a*s n) (b*s n)) x ∧
      rawCount (spatialAnnulus (a*s n) (b*s n)) x ≤
        packetMass g c₁ (r₀ n) (s n) (spatialAnnulus ((a-η)*s n) ((b+η)*s n)) x := by
  have hd : Tendsto (fun n => (c₁*s n^packetExponent)*b) atTop (𝓝 0) := by
    simpa using (packet_relative_width_tendsto hs c₁).mul_const b
  filter_upwards [hsp, hrp, hd.eventually_lt_const hη,
    (packet_clamp_tendsto hs hr c₁).eventually_lt_const (sub_pos.mpr hηa)]
    with n hsn hrn hδ hcl x
  exact packetMass_annulus_sandwich g hgnorm hgsupp hc hrn hsn ha hab hη hηa hδ
    ((div_lt_iff₀ hsn).mp hcl).le x

theorem nuclear_clamp_ratio {Z s ε : ℝ} (hZ : 0 < Z) (hs : 0 < s) :
    (ε * Z^(-(1/3:ℝ)))/s = ε * (Z*s^3)^(-(1/3:ℝ)) := by
  rw [Real.mul_rpow hZ.le (pow_nonneg hs.le 3),
    ← Real.rpow_natCast_mul hs.le 3 (-(1/3:ℝ))]
  norm_num [Real.rpow_neg_one]
  ring

theorem nuclear_clamp_tendsto {Z s : ℕ → ℝ} (hZ : ∀ᶠ n in atTop, 0 < Z n)
    (hs : ∀ᶠ n in atTop, 0 < s n)
    (hmass : Tendsto (fun n => Z n*s n^3) atTop atTop) (ε : ℝ) :
    Tendsto (fun n => (ε*(Z n)^(-(1/3:ℝ)))/s n) atTop (𝓝 0) := by
  have h := ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/3)).comp hmass).const_mul ε
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [hZ,hs] with n hzn hsn
  exact (nuclear_clamp_ratio hzn hsn).symm

theorem tendsto_of_parameter_sandwich {α β : Type*} {l : Filter α} {p : Filter β}
    [p.NeBot] {f : α → ℝ} {g h : β → α → ℝ} {a b : β → ℝ} {L : ℝ}
    (ha : Tendsto a p (𝓝 L)) (hb : Tendsto b p (𝓝 L))
    (hs : ∀ᶠ t in p,
      Tendsto (g t) l (𝓝 (a t)) ∧ Tendsto (h t) l (𝓝 (b t)) ∧
      ∀ᶠ n in l, g t n ≤ f n ∧ f n ≤ h t n) :
    Tendsto f l (𝓝 L) := by
  apply tendsto_order.mpr
  constructor
  · intro x hx
    obtain ⟨t,ht,hs'⟩ := (ha.eventually (lt_mem_nhds hx) |>.and hs).exists
    filter_upwards [hs'.1.eventually (lt_mem_nhds ht), hs'.2.2] with n hn hn'
    exact hn.trans_le hn'.1
  · intro x hx
    obtain ⟨t,ht,hs'⟩ := (hb.eventually (gt_mem_nhds hx) |>.and hs).exists
    filter_upwards [hs'.2.1.eventually (gt_mem_nhds ht), hs'.2.2] with n hn hn'
    exact hn'.2.trans_lt hn

theorem raw_annulus_tendsto_of_packet_sandwich
    {T : ℕ → ℝ → ℝ → ℝ} {N : ℕ → ℝ} {a b C : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hT : ∀ u v : ℝ, 0 < u → u < v →
      Tendsto (fun n => T n u v) atTop (𝓝 (C/u^3-C/v^3)))
    (hs : ∀ η : ℝ, 0 < η → η < min a ((b-a)/2) →
      ∀ᶠ n in atTop, T n (a+η) (b-η) ≤ N n ∧ N n ≤ T n (a-η) (b+η)) :
    Tendsto N atTop (𝓝 (C/a^3-C/b^3)) := by
  have hb : 0 < b := ha.trans hab
  apply tendsto_of_parameter_sandwich (p := 𝓝[>] (0 : ℝ))
    (g := fun η n => T n (a+η) (b-η)) (h := fun η n => T n (a-η) (b+η))
    (a := fun η => C/(a+η)^3-C/(b-η)^3)
    (b := fun η => C/(a-η)^3-C/(b+η)^3)
  · have hcont : ContinuousAt (fun η : ℝ => C/(a+η)^3-C/(b-η)^3) 0 := by
      fun_prop (disch := positivity)
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  · have hcont : ContinuousAt (fun η : ℝ => C/(a-η)^3-C/(b+η)^3) 0 := by
      fun_prop (disch := positivity)
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  · have hm : 0 < min a ((b-a)/2) := lt_min ha (by linarith)
    filter_upwards [self_mem_nhdsWithin, (gt_mem_nhds hm : ∀ᶠ η : ℝ in 𝓝 0, η < min a ((b-a)/2)).filter_mono nhdsWithin_le_nhds]
      with η hη hηm
    have hη0 : 0 < η := hη
    have hηa : η < a := hηm.trans_le (min_le_left _ _)
    have hηab : η < (b-a)/2 := hηm.trans_le (min_le_right _ _)
    exact ⟨hT _ _ (by linarith) (by linarith),
      hT _ _ (by linarith) (by linarith), hs η hη0 hηm⟩

theorem rawCount_memLp_measure {n : ℕ} (μ : Measure (Configuration n))
    [IsFiniteMeasure μ] {S : Set Position} (hS : MeasurableSet S) :
    MemLp (rawCount (n := n) S) 2 μ := by
  apply MemLp.of_bound (measurable_rawCount hS).aestronglyMeasurable (n : ℝ)
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (rawCount_nonneg S x)] using rawCount_le_number S x

theorem expected_raw_annulus_of_packets {s r₀ : ℕ → ℝ} (N : ℕ → ℕ)
    (μ : ∀ n, Measure (Configuration (N n))) [∀ n, IsFiniteMeasure (μ n)]
    (g : Position → ℝ) (hg : Continuous g) (hgnorm : (∫ y, g y^2) = 1)
    (hgsupp : ∀ x, 1 < ‖x‖ → g x = 0) {c₁ a b C : ℝ}
    (hc : 0 < c₁) (ha : 0 < a) (hab : a < b)
    (hsp : ∀ᶠ n in atTop, 0 < s n) (hrp : ∀ᶠ n in atTop, 0 < r₀ n)
    (hs : Tendsto s atTop (𝓝 0))
    (hr : Tendsto (fun n => r₀ n/s n) atTop (𝓝 0))
    (hpacket : ∀ u v : ℝ, 0 < u → u < v →
      Tendsto (fun n => s n^3 * ∫ x,
        packetMass g c₁ (r₀ n) (s n) (spatialAnnulus (u*s n) (v*s n)) x ∂μ n)
        atTop (𝓝 (C/u^3-C/v^3))) :
    Tendsto (fun n => s n^3 * ∫ x,
      rawCount (spatialAnnulus (a*s n) (b*s n)) x ∂μ n)
      atTop (𝓝 (C/a^3-C/b^3)) := by
  apply raw_annulus_tendsto_of_packet_sandwich ha hab hpacket
  intro η hη hηm
  have hηa := hηm.trans_le (min_le_left _ _)
  filter_upwards [hsp, hrp,
    eventually_packet_sandwich N g hgnorm hgsupp hc ha hab hη hηa hsp hrp hs hr]
    with n hsn hrn hsan
  have hraw := (rawCount_memLp_measure (μ n)
    (measurableSet_spatialAnnulus (a*s n) (b*s n))).integrable (by norm_num)
  have hlow := (packetMass_memLp hg hgnorm hc hrn hsn
    (spatialAnnulus ((a+η)*s n) ((b-η)*s n)) (μ n)).integrable (by norm_num)
  have hhigh := (packetMass_memLp hg hgnorm hc hrn hsn
    (spatialAnnulus ((a-η)*s n) ((b+η)*s n)) (μ n)).integrable (by norm_num)
  exact ⟨mul_le_mul_of_nonneg_left (integral_mono hlow hraw (fun x => (hsan x).1))
      (pow_nonneg hsn.le 3),
    mul_le_mul_of_nonneg_left (integral_mono hraw hhigh (fun x => (hsan x).2))
      (pow_nonneg hsn.le 3)⟩

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
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_RetainedGoodEvent
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

theorem PropagationDatum.valid_event {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B C r Z L M : ℝ}
    {μ : Ω → Position → ℝ} (d : PropagationDatum P B C r Z L μ)
    (hcost : (∫ o,(∫ x,d.error o x) ∂P) ≤ M) :
    ∃ V : Set Ω,MeasurableSet V ∧ P.real Vᶜ ≤ M ∧
      ∀ o∈V,PropagationInvariant B C r Z L (d.offset o) (μ o) (d.error o) ∧
        Integrable (d.error o) ∧ (∫ x,d.error o x) ≤ 1 := by
  let bad := {o | ¬(PropagationInvariant B C r Z L (d.offset o) (μ o) (d.error o) ∧ Integrable (d.error o))}
  have hbad : P bad = 0 := by
    apply ae_iff.mp
    filter_upwards [d.invariant,d.error_product_integrable.prod_right_ae] with o ho hi
    exact ⟨ho,hi⟩
  let W := (toMeasurable P bad)ᶜ
  have hW : MeasurableSet W := (measurableSet_toMeasurable P bad).compl
  have hWzero : P.real Wᶜ = 0 := by simp only [W,compl_compl,Measure.real,measure_toMeasurable,hbad,ENNReal.toReal_zero]
  let X := fun o => ∫ x,d.error o x
  have hXm : Measurable X := d.error_measurable.stronglyMeasurable.integral_prod_right.measurable
  have hXi : Integrable X P := d.error_product_integrable.integral_prod_left
  have hXp : 0 ≤ᵐ[P] X := d.invariant.mono (fun o ho => integral_nonneg ho.nonnegative_error)
  let A := {o | X o ≤ 1}
  have hA : MeasurableSet A := measurableSet_le hXm measurable_const
  have hAp : P.real Aᶜ ≤ M := by
    calc
      P.real Aᶜ ≤ P.real {o | 1 ≤ X o} := measureReal_mono (by intro o ho; change ¬ X o ≤ 1 at ho; exact (lt_of_not_ge ho).le)
      _ ≤ ∫ o,X o ∂P := by simpa only [one_mul] using mul_meas_ge_le_integral_of_nonneg hXp hXi 1
      _ ≤ M := hcost
  refine ⟨W∩A,hW.inter hA,?_,?_⟩
  · rw [compl_inter]
    exact (measureReal_union_le _ _).trans (by simpa only [hWzero,zero_add] using add_le_add (le_refl (P.real Wᶜ)) hAp)
  · intro o ho
    have hb : o∉bad := fun hb => ho.1 (subset_toMeasurable P bad hb)
    exact ⟨(not_not.mp hb).1,(not_not.mp hb).2,ho.2⟩

end NeutralAtom
end

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

theorem slow_stages {P : ℕ → ℕ → Prop}
    (hP : ∀ q : ℕ, ∀ᶠ n : ℕ in atTop, P q n) :
    ∃ q : ℕ → ℕ, Tendsto q atTop atTop ∧ ∀ᶠ n in atTop, P (q n) n := by
  classical
  let q : ℕ → ℕ := fun n => Nat.findGreatest (fun k => P k n) n
  refine ⟨q, tendsto_atTop.mpr ?_, ?_⟩
  · intro Q
    filter_upwards [eventually_ge_atTop Q, hP Q] with n hn hpn
    exact Nat.le_findGreatest hn hpn
  · filter_upwards [hP 0] with n hn
    exact Nat.findGreatest_spec (P := fun k => P k n) (Nat.zero_le n) hn

end NeutralAtom
end

end
section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal NNReal Classical
noncomputable section
namespace NeutralAtom
lemma dyadic_radius_choice {r₀ s q : ℝ} (hr : 0 < r₀) (hs : 0 < s) (hq : 0 < q)
    (hsmall : r₀/s ≤ q⁻¹) :
    ∃ j : ℕ, s/(2*q) ≤ r₀*2^j ∧ r₀*2^j ≤ s/q := by
  have hrq : r₀*q ≤ s := by
    have H := (div_le_iff₀ hs).mp hsmall
    have H' := mul_le_mul_of_nonneg_right H hq.le
    calc
      r₀*q ≤ q⁻¹*s*q := H'
      _ = s := by field_simp
  have hx : 1 ≤ s/(q*r₀) := (one_le_div (mul_pos hq hr)).mpr (by simpa [mul_comm] using hrq)
  obtain ⟨j,hj,hj'⟩ := exists_nat_pow_near hx (by norm_num : (1:ℝ)<2)
  refine ⟨j,?_,?_⟩
  · have H' := (div_lt_iff₀ (mul_pos hq hr)).mp hj'
    rw [pow_succ] at H'
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*q)).mpr
    nlinarith only [H',pow_pos (by norm_num : (0:ℝ)<2) j]
  · have H := (le_div_iff₀ (mul_pos hq hr)).mp hj
    apply (le_div_iff₀ hq).mpr
    nlinarith only [H]
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_PhysicalRetainedDatum
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

theorem physical_finite_retained_datum {N K J : ℕ} (Z : ℕ) (hZ : 1 ≤ Z)
    {ψ : Wavefunction (N+1)} {g : Gradient (N+1)} (hd : FormDomain ψ g) (hn : normSquared ψ=1)
    {g₀ : 𝓢(Position,ℝ)} (hgs : ∀ x,1<‖x‖ → g₀ x=0) (hm : (∫ x,g₀ x^2)=1)
    {c ε B C r₀ s M : ℝ} (hc : 0 < c) (hε : 0<ε) (hB : 0<B) (hBC : B ≤ C)
    (hr : 0 < r₀) (hr1 : r₀ ≤ 1) (hs : 0 < s) (hM : 0 ≤ M)
    (_ : c*s^packetExponent ≤ 1/4) (hcubic : (Z:ℝ)*r₀^3=ε^3)
    (hnum : (N+1:ℝ) ≤ 3*(Z:ℝ)) (hBe : B ≤ ε^3/10) (heC : 32*ε^3 ≤ C)
    (hR : tfReaction (2*ε^3) ≤ (3/40:ℝ)*ε^3) (hbar : 4*Real.pi*kTF*Real.sqrt B ≤ 19/2)
    (k : PropagationConstants B C) :
    letI := rawLaw_isProbability hd.2.2.1 hn
    let P := observationLaw K (rawLaw ψ)
    let rs := fun j : Fin K => r₀*2^j.val
    let μ := fun j o => conditionalPacketDensity P Prod.fst (tailObservation rs j) g₀ c r₀ s (tailObservation rs j o)
    ∀ {G₀ : Set (Fin K → UnorderedArray (N+1))},MeasurableSet G₀ →
      P.real (tailObservation rs 0 ⁻¹' G₀ᶜ) ≤ 343*r₀^35 →
      (∀ a∈G₀,∀ x,r₀ ≤ ‖x‖ → ‖x‖ ≤ 2*r₀ →
        potentialOf (conditionalPacketDensity P Prod.fst (tailObservation rs 0) g₀ c r₀ s a) x ≤ (1/10:ℝ)*(Z:ℝ)/r₀) →
    ∀ (G : Fin J → Set (ObservationSample (N+1) K)),
      (∀ j,MeasurableSet (G j)) →
      (∀ j,∀ o∈G j,∀ x,(r₀*2^j.val) ≤ ‖x‖ → ‖x‖ ≤ 4*k.L*(r₀*2^j.val) →
        let F := (Z:ℝ)*coulombKernel x-potentialOf (μ j.val o) x
        F ≤ C/‖x‖^4 ∧ ∀ h∈Icc (B/2) C,
          (Coulomb.tfScalarDensity h ≤ ‖x‖^6*μ j.val o x → h-k.ξ ≤ ‖x‖^4*F) ∧
          (‖x‖^6*μ j.val o x ≤ Coulomb.tfScalarDensity h → ‖x‖^4*F ≤ h+k.ξ)) →
      (∀ j,(∫ o in (G j)ᶜ,∫ x in {x : Position | (r₀*2^j.val) ≤ ‖x‖ ∧ ‖x‖<2*(r₀*2^j.val)},μ j.val o x ∂volume ∂P) ≤ M*(r₀*2^j.val)^9) →
    ∃ d : PropagationDatum P B C (r₀*2^J) (Z:ℝ) k.L (μ J),
      (∫ o,(∫ x,d.error o x) ∂P) ≤ (1029*ε^3+M)*(r₀*2^J)^9 := by
  have := rawLaw_isProbability hd.2.2.1 hn
  dsimp only
  let P := observationLaw K (rawLaw ψ)
  let rs := fun j : Fin K => r₀*2^j.val
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
  exact ⟨d,hd'⟩
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RadialBounds_PhysicalBarrierData
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

theorem physical_barrier_data : ∃ ε B C L M : ℝ,0<ε ∧ 0<B ∧ 0 ≤ C ∧ 0 ≤ M ∧
    ∀ D : ℝ,0 ≤ D → ∃ s₀:ℝ,0 < s₀ ∧ s₀ ≤ 1 ∧ ∀ s:ℝ,0 < s → s < s₀ →
    ∃ Zmin:ℕ,∀ Z:ℕ,Zmin ≤ Z → ∀ (hZ:1 ≤ Z) {N K:ℕ}
      {ψ:Wavefunction (N+1)} {g:Gradient (N+1)},
    ∀ (hd:FormDomain ψ g) (hn:normSquared ψ=1),
    (∀ (χ:Wavefunction (N+1)) (h:Gradient (N+1)),FormDomain χ h → normSquared χ=1 →
      energy Z ψ g ≤ energy Z χ h) →
    ∀ {E:ℝ},(E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E+D → (N+1:ℝ) ≤ 3*(Z:ℝ) →
    letI := rawLaw_isProbability hd.2.2.1 hn
    let r₀ := initialAtomicRadius ε (Z:ℝ)
    let P := observationLaw K (rawLaw ψ)
    let rs := fun j : Fin K => r₀*2^j.val
    ∀ (j : Fin K), rs j  ≤  s →
    ∃ d:PropagationDatum P B C (rs j) (Z:ℝ) L
      (fun o => conditionalPacketDensity P Prod.fst (tailObservation rs j.val)
        Coulomb.unitWindow 1 r₀ s (tailObservation rs j.val o)),
      (∫ o,(∫ x,d.error o x) ∂P) ≤ M*(rs j)^9 := by
  obtain ⟨εmax,hεmax,HI⟩ := physical_initial_event
  obtain ⟨ε,B,hε,hεceil,hB,hBe,hR,hbar⟩ := initial_constants_exist hεmax
  let C := max physicalSpatialCap (max B (32*ε^3))
  have hBC : B  ≤  C := (le_max_left _ _).trans (le_max_right _ _)
  have hcapC : physicalSpatialCap  ≤  C := le_max_left _ _
  have heC : 32*ε^3  ≤  C := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨k⟩ := propagation_constants_exist hB hBC
  obtain ⟨Kprob,hK,HG⟩ := physical_propagation_good_events Coulomb.unitWindow Coulomb.unitWindow_support
    Coulomb.unitWindow_mass Coulomb.unitWindow_radial (by norm_num : (0:ℝ)<1) hB hBC hcapC k
  obtain ⟨M,hM,HC⟩ := physical_bad_shell_error
  let T := 1029*ε^3+M*Real.sqrt Kprob
  have hT : 0  ≤  T := by dsimp [T]; positivity
  refine ⟨ε,B,C,k.L,T,hε,hB,hB.le.trans hBC,hT,?_⟩
  intro D hD
  obtain ⟨s₀,hs₀,hs₀1,hgates,HG⟩ := HG D hD
  refine ⟨s₀,hs₀,hs₀1,?_⟩
  intro s hs hss
  have hs1 : s  ≤  1 := hss.le.trans hs₀1
  obtain ⟨hq1,hq2,hDs⟩ := hgates hs hss
  obtain ⟨Zi,Hi⟩ := HI hε hεceil D Coulomb.unitWindow Coulomb.unitWindow_mass
    Coulomb.unitWindow_radial Coulomb.unitWindow_support (by norm_num : (0:ℝ)<1) hs hq1
  refine ⟨Zi,?_⟩
  intro Z hZi hZ N K ψ g hd hn hmin E hE he hnum
  have := rawLaw_isProbability hd.2.2.1 hn
  dsimp only
  intro j hjs
  have hZpos : 0<(Z:ℝ) := by exact_mod_cast (zero_lt_one.trans_le hZ)
  let r₀ := initialAtomicRadius ε (Z:ℝ)
  have hr : 0 < r₀ := initialAtomicRadius_pos hε hZpos
  have hrs : r₀ ≤ s := (le_mul_of_one_le_right hr.le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n:=j.val))).trans hjs
  have hr1 : r₀ ≤ 1 := hrs.trans hs1
  let P := observationLaw K (rawLaw ψ)
  let rs := fun l:Fin K => r₀*2^l.val
  let ix : Fin j.val → Fin K := fun l => ⟨l.val,l.isLt.trans j.isLt⟩
  have hscale (l:Fin j.val) : rs (ix l) ≤ s :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) l.isLt.le) hr.le).trans hjs
  have hge (l:Fin j.val) : r₀ ≤ rs (ix l) := le_mul_of_one_le_right hr.le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  obtain ⟨G₀,hG₀,hp₀,hlo⟩ := Hi Z hZi hZ (J:=K) hd hn hmin hE he hnum
  have HG' := fun l : Fin j.val => HG Z hZ hd hn hmin hE he hr hs hss (ix l) (hscale l)
  choose G hG hp HGood using HG'
  have hcost (l : Fin j.val) :
      (∫ o in (G l)ᶜ,∫ y in {y : Position | rs (ix l)  ≤  ‖y‖ ∧ ‖y‖<2*(rs (ix l))},
        conditionalPacketDensity P Prod.fst (tailObservation rs l.val) Coulomb.unitWindow 1 r₀ s
          (tailObservation rs l.val o) y ∂volume ∂P)  ≤  M*Real.sqrt Kprob*(rs (ix l))^9 := by
    exact HC Z hZ hd hn hE he hD Coulomb.unitWindow.continuous Coulomb.unitWindow_mass
      Coulomb.unitWindow_support (by norm_num : (0:ℝ)<1) hr hs (hge l) ((hscale l).trans hs1)
      ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hr.trans_le (hge l)).le (hscale l) 7) hD).trans hDs)
      hq2 hK.le rs l.val (hG l).2.compl (hp l)
  have HF := physical_finite_retained_datum Z hZ hd hn Coulomb.unitWindow_support Coulomb.unitWindow_mass
    (by norm_num : (0:ℝ)<1) hε hB hBC hr hr1 hs (mul_nonneg hM (Real.sqrt_nonneg Kprob)) hq2
    (initialAtomicRadius_cubic hZpos) hnum hBe heC hR hbar k hG₀ hp₀ hlo G
    (fun j => (hG j).1) HGood hcost
  exact HF
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_QuantumProfileDatum
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

lemma profile_band_coverage {s q r : ℝ} (hq : 2 ≤ q) (hs : 0 < s)
    (hl : s/(2*q) ≤ r) : q*s ≤ 4*q^2*r := by
  have hqpos : 0 < q := by linarith only [hq]
  have H := (div_le_iff₀ (by positivity : (0:ℝ)<2*q)).mp hl
  have H' := mul_le_mul_of_nonneg_left H hqpos.le
  have hr : 0 ≤ r := (div_pos hs (by positivity)).le.trans hl
  nlinarith only [H',sq_nonneg q,mul_nonneg (sq_nonneg q) hr]

theorem physical_profile_constants : ∃ ε B C L M : ℝ,0 < ε ∧ 0 < B ∧ 0 ≤ M ∧
    ∃ Zbar : ℝ → ℕ, ∀ q : ℝ,2 ≤ q → ∃ Cq : ℝ,0 < Cq ∧
      ∃ sq : ℝ,0 < sq ∧ ∀ {N : ℕ} (ψ : Wavefunction (N+1)),
        ∀ hψ : IsNormalizedGroundState (N+1) ψ, ∀ s : ℝ,0 < s → s < sq → Zbar s ≤ N+1 →
        initialAtomicRadius ε ((N+1:ℕ):ℝ)/s ≤ q⁻¹ →
         let := rawLaw_isProbability (hψ.choose_spec.1.2.2.1)
          (hψ.choose_spec.2.1)
        Nonempty (QuantumProfileDatum ψ ε B C L M s q Cq) := by
  obtain ⟨ε,B,C,L,M,hε,hB,hC,hM,HB⟩ := physical_barrier_data
  obtain ⟨D,hD,Zmin,Henergy⟩ := physical_neutral_energy_offset
  obtain ⟨sB,hsB,hsB1,HB⟩ := HB D hD
  choose ZB HZB using HB
  let Zbar := fun s => max Zmin (if H : 0 < s ∧ s < sB then ZB s H.1 H.2 else 0)
  refine ⟨ε,B,C,L,M,hε,hB,hM,Zbar,?_⟩
  intro q hq
  obtain ⟨Cq,hCq,Hinv⟩ := physical_tf_band hq
  obtain ⟨sI,hsI,hsI1,Hinv⟩ := Hinv D hD
  refine ⟨Cq,hCq,min sB sI,lt_min hsB hsI,?_⟩
  intro N ψ hψ s hs hss hZbar hsmall
  have hZm : Zmin ≤ N+1 := (le_max_left ..).trans hZbar
  have hsBs : s < sB := hss.trans_le (min_le_left ..)
  have hsIs : s < sI := hss.trans_le (min_le_right ..)
  have hZB : ZB s hs hsBs ≤ N+1 := by
    have H := (le_max_right Zmin _).trans hZbar
    simpa only [Zbar,dite_eq_left (show 0 < s ∧ s < sB from ⟨hs,hsBs⟩)] using H
  obtain ⟨g,hd,hn,hmin⟩ := hψ
  have := rawLaw_isProbability hd.2.2.1 hn
  have hZ : 1 ≤ N+1 := by omega
  have hZpos : 0 < ((N+1:ℕ):ℝ) := by positivity
  have hr₀ := initialAtomicRadius_pos hε hZpos
  obtain ⟨j,hjl,hju⟩ := dyadic_radius_choice hr₀ hs (by linarith only [hq]) hsmall
  have hq1 : 1 ≤ q := by linarith only [hq]
  have hrjs : profileRadius ε N j ≤ s := hju.trans ((div_le_self hs.le hq1))
  have he := Henergy (N+1) hZm hZ hd hn hmin
  have hE := Coulomb.atom_unrestricted_bottom_real (N+1) hZ
    (asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1) (asH1_antisymmetric hd) ((asH1_mass ..).trans hn)
  obtain ⟨d,hdcost⟩ := HZB s hs hsBs (N+1) hZB hZ hd hn hmin hE.le he
    (show (N+1:ℝ) ≤ 3*((N+1:ℕ):ℝ) by push_cast; nlinarith only [Nat.cast_nonneg (α:=ℝ) N]) (K:=j+1) ⟨j,by omega⟩ hrjs
  obtain ⟨V,hV,hVp,HV⟩ := d.valid_event hdcost
  obtain ⟨G,hG,hGp,HG⟩ := Hinv (N+1) hZ hd hn hmin hE.le he hr₀ hs hsIs
    (J:=j+1) ⟨j,by omega⟩ hrjs
  refine ⟨⟨j,hjl,hju,d,V∩G,hV.inter hG,?_,?_,?_⟩⟩
  · rw [compl_inter]
    exact (measureReal_union_le Vᶜ Gᶜ).trans ((add_le_add hVp hGp).trans
      (add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
        (mul_pos hr₀ (by positivity)).le hrjs 9) hM) le_rfl))
  · intro o ho
    exact HV o ho.1
  · intro o ho x hx hxq
    exact HG o ho.2 x hx (hxq.trans (profile_band_coverage hq hs hjl))
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
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal
namespace NeutralAtom
theorem Admissible.charge_tendsto {Zbar : ℝ → ℕ} {s : ℕ → ℝ} {N : ℕ → ℕ}
    (h : Admissible Zbar s N) : Tendsto (fun n => N n+1) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [h.1, h.2.1.eventually_lt_const (by norm_num : (0:ℝ) < 1),
    h.2.2.2.eventually_ge_atTop (b : ℝ)] with n hsp hs1 hb
  have hs3 : s n^3 ≤ 1 := pow_le_one₀ hsp.le hs1.le
  have hz : (b : ℝ) ≤ (N n+1 : ℝ) := hb.trans
    (mul_le_of_le_one_right (by positivity) hs3)
  exact_mod_cast hz

theorem expected_exterior_of_raw_annuli (hcount : UniformGroundStateCountControl)
    (s : ℕ → ℝ) (N : ℕ → ℕ) (ψ : ∀ n, Wavefunction (N n+1))
    (hψ : ∀ n, IsNormalizedGroundState (N n+1) (ψ n))
    (hsp : ∀ n, 0 < s n) (hs : Tendsto s atTop (𝓝 0))
    (hN : Tendsto (fun n => N n+1) atTop atTop)
    (hann : ∀ a b, 0 < a → a < b →
      Tendsto (fun n => s n^3 * ∫ x,
        rawCount (spatialAnnulus (a*s n) (b*s n)) x ∂rawLaw (ψ n))
        atTop (𝓝 ((81*Real.pi^2/2)/a^3-(81*Real.pi^2/2)/b^3)))
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => s n^3 * exteriorMass (ψ n) (a*s n))
      atTop (𝓝 ((81*Real.pi^2/2)/a^3)) := by
  obtain ⟨A,B,Z₀,hA,_hB,hbound⟩ := small_shell_bounds_of_count_control hcount
  have hint : ∀ n σ, MemLp (ψ n σ) 2 volume := fun n => (hψ n).choose_spec.1.2.2.1
  have hanti : ∀ n, IsAntisymmetric (ψ n) := fun n => (hψ n).choose_spec.1.1
  apply tails_converge_of_annuli (β := fun n => B*s n^3) (D := (8/7:ℝ)*A)
    (by positivity : 0 ≤ 81*Real.pi^2/2) ha
  · simpa using (hs.pow 3).const_mul B
  · exact fun n r => mul_nonneg (pow_nonneg (hsp n).le 3) (exteriorMass_nonneg (ψ n) _)
  · intro M hM
    filter_upwards [hN.eventually_ge_atTop Z₀] with n hn
    obtain ⟨hfar,hshell⟩ := hbound (N n) (ψ n) hn (hψ n)
    exact scaled_dyadic_tail_bound hA (exteriorMass_antitone (hint n)) hfar hshell (hsp n) hM
  · intro M haM
    have heq : (fun n => s n^3 * exteriorMass (ψ n) (a*s n) -
        s n^3 * exteriorMass (ψ n) (M*s n)) =
        (fun n => s n^3 * ∫ x,
          rawCount (spatialAnnulus (a*s n) (M*s n)) x ∂rawLaw (ψ n)) := by
      funext n
      rw [← mul_sub, exteriorMass_sub (hint n)
        (mul_le_mul_of_nonneg_right haM.le (hsp n).le), integral_rawLaw (hint n),
        rawExpectation_count_eq_density (hanti n) (hint n) (measurableSet_spatialAnnulus _ _)]
    simpa only [heq] using hann a M ha haM

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_LimitTheory_AdmissibleStage
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

theorem admissible_profile_stages {Zbar : ℝ → ℕ} {s : ℕ → ℝ} {N : ℕ → ℕ}
    (had : Admissible Zbar s N) (ε : ℝ) (Cq sq : ℕ → ℝ) (hsq : ∀ k,0 < sq k) :
    ∃ k : ℕ → ℕ,Tendsto k atTop atTop ∧ ∀ᶠ n in atTop,
      0 < s n ∧ s n < sq (k n) ∧ Zbar (s n) ≤ N n+1 ∧
      Cq (k n)*s n^25 ≤ (((k n+2:ℕ):ℝ))⁻¹ ∧
      initialAtomicRadius ε ((N n+1:ℕ):ℝ)/s n ≤ (((k n+2:ℕ):ℝ))⁻¹ := by
  have hc : Tendsto (fun n => initialAtomicRadius ε ((N n+1:ℕ):ℝ)/s n) atTop (𝓝 0) := by
    simpa only [initialAtomicRadius,Nat.cast_add,Nat.cast_one] using nuclear_clamp_tendsto
      (Eventually.of_forall (fun n => (by positivity : (0:ℝ)<(N n+1:ℝ)))) had.1 had.2.2.2 ε
  apply slow_stages (P:=fun k n =>
    0 < s n ∧ s n < sq k ∧ Zbar (s n) ≤ N n+1 ∧
    Cq k*s n^25 ≤ (((k+2:ℕ):ℝ))⁻¹ ∧
    initialAtomicRadius ε ((N n+1:ℕ):ℝ)/s n ≤ (((k+2:ℕ):ℝ))⁻¹)
  intro k
  have HK : 0 < (((k+2:ℕ):ℝ))⁻¹ := by positivity
  have Hp : Tendsto (fun n => Cq k*s n^25) atTop (𝓝 0) := by simpa using (had.2.1.pow 25).const_mul (Cq k)
  filter_upwards [had.1,had.2.1.eventually_lt_const (hsq k),had.2.2.1,
    Hp.eventually_lt_const HK,hc.eventually_lt_const HK] with n hs hsq hZ hp hc
  exact ⟨hs,hsq,hZ,hp.le,hc.le⟩

lemma shifted_stage_tendsto {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) (K : ℕ) :
    Tendsto (fun n => k (n+K)+2) atTop atTop := by
  exact (tendsto_add_atTop_nat 2).comp (hk.comp (tendsto_add_atTop_nat K))
end NeutralAtom
end

end
section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal NNReal Classical
noncomputable section
namespace NeutralAtom

theorem physical_expected_exterior_asymptotic : ∃ Zbar : ℝ → ℕ,ExpectedExteriorAsymptotic Zbar := by
  obtain ⟨ε,B,C,L,M,hε,hB,hM,Zbar,Hdata⟩ := physical_profile_constants
  have HG := fun k : ℕ => Hdata ((k+2:ℕ):ℝ) (by exact_mod_cast (show 2 ≤ k+2 by omega))
  choose Cq hCq sq hsq HD using HG
  refine ⟨Zbar,?_⟩
  intro s N had ψ hψ a ha
  let : ∀ n,IsProbabilityMeasure (rawLaw (ψ n)) := fun n =>
    rawLaw_isProbability (hψ n).choose_spec.1.2.2.1 (hψ n).choose_spec.2.1
  obtain ⟨k,hk,hgood⟩ := admissible_profile_stages had ε Cq sq hsq
  obtain ⟨K,hK⟩ := eventually_atTop.mp hgood
  have Hstage (n : ℕ) := hK (n+K) (Nat.le_add_left K n)
  let s' := fun n => s (n+K)
  let N' := fun n => N (n+K)
  let ψ' := fun n => ψ (n+K)
  let q := fun n => k (n+K)+2
  let Cq' := fun n => Cq (k (n+K))
  have hsp : ∀ n,0 < s' n := fun n => (Hstage n).1
  have hs : Tendsto s' atTop (𝓝 0) := had.2.1.comp (tendsto_add_atTop_nat K)
  have hz : Tendsto (fun n => N' n+1) atTop atTop := had.charge_tendsto.comp (tendsto_add_atTop_nat K)
  have hq : Tendsto q atTop atTop := shifted_stage_tendsto hk K
  have hpr : ∀ n,0 < initialAtomicRadius ε ((N' n+1:ℕ):ℝ) :=
    fun n => initialAtomicRadius_pos hε (by positivity)
  have hr : Tendsto (fun n => initialAtomicRadius ε ((N' n+1:ℕ):ℝ)/s' n) atTop (𝓝 0) := by
    have HR : Tendsto (fun n => initialAtomicRadius ε ((N n+1:ℕ):ℝ)/s n) atTop (𝓝 0) := by
      simpa only [initialAtomicRadius,Nat.cast_add,Nat.cast_one] using nuclear_clamp_tendsto
        (Eventually.of_forall (fun n => (by positivity : (0:ℝ)<(N n+1:ℝ)))) had.1 had.2.2.2 ε
    exact HR.comp (tendsto_add_atTop_nat K)
  have hdn (n : ℕ) : Nonempty (QuantumProfileDatum (ψ' n) ε B C L M (s' n) (q n:ℝ) (Cq' n)) :=
    HD (k (n+K)) (ψ (n+K)) (hψ (n+K)) (s (n+K)) (Hstage n).1 (Hstage n).2.1
      (Hstage n).2.2.1 (Hstage n).2.2.2.2
  let d := fun n => Classical.choice (hdn n)
  have hp : ∀ n,Cq' n*s' n^25 ≤ (q n:ℝ)⁻¹ := fun n => (Hstage n).2.2.2.1
  have hpacket (a b : ℝ) (ha : 0 < a) (hab : a < b) := quantum_profile_packet_limit
    N' ψ' (fun n => hψ (n+K)) hε hB hM s' hsp hs hz hr q hq Cq' d hp ha hab
  have hann (a b : ℝ) (ha : 0 < a) (hab : a < b) := expected_raw_annulus_of_packets
    (fun n => N' n+1) (fun n => rawLaw (ψ' n)) Coulomb.unitWindow Coulomb.unitWindow.continuous
    Coulomb.unitWindow_mass Coulomb.unitWindow_support (by norm_num : (0:ℝ)<1) ha hab
    (Eventually.of_forall hsp) (Eventually.of_forall hpr) hs hr hpacket
  have htail := expected_exterior_of_raw_annuli physical_uniform_count_control s' N' ψ'
    (fun n => hψ (n+K)) hsp hs hz hann ha
  apply (tendsto_add_atTop_iff_nat K).mp
  simpa only [s',N',ψ',bTF_cube] using htail
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
noncomputable section
namespace NeutralAtom

theorem generalized_outer_radii_oai
    (Ψ : ∀ N : ℕ, Wavefunction (N + 1))
    (hΨ : ∀ N : ℕ, IsNormalizedGroundState (N + 1) (Ψ N)) :
    Tendsto (fun m : ℕ => (((m : ℝ) ^ (1 / 3 : ℝ) : ℝ) : EReal) * upperRadius Ψ m)
      atTop (𝓝 (bTF : EReal)) ∧
    Tendsto (fun m : ℕ => (((m : ℝ) ^ (1 / 3 : ℝ) : ℝ) : EReal) * lowerRadius Ψ m)
      atTop (𝓝 (bTF : EReal)) := by
  obtain ⟨Zbar,htail⟩ := physical_expected_exterior_asymptotic
  exact iterated_limits_of_expected_exterior_asymptotic Zbar htail Ψ hΨ
end NeutralAtom
end

end

end OAI
end

theorem solution : type_of% @OAI.NeutralAtom.generalized_outer_radii_oai := @OAI.NeutralAtom.generalized_outer_radii_oai
