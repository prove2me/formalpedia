-- Prove2me | solution 1 for OAI.Coulomb.atomic_predecessor_from_physical_mean
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:27:25.917671+00:00
-- url     : https://prove2.me/submissions/f016a3e0-159f-4c75-a74d-0d7e2214061a

import Mathlib
import Definitions.Def_CoulombRadii
import Definitions.Def_OAIQ062C008
import Theorems.Thm_OAI_Coulomb_RecordedEnsemble_atomic_zero_offset_core_deletion

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

theorem rawCount_nonneg {n : ℕ} (S : Set Position) (x : Configuration n) :
    0 ≤ rawCount S x := by
  apply Finset.sum_nonneg
  intro i _
  by_cases hi : x i ∈ S <;> simp [hi]

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
-- module Solutions.OAIQ062_CR.CoulombRadii_LimitTheory_AtomicOutKinetic
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

lemma slice_core_form_ge_baseline {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    (ha : ∀ s, ∀ᵐ x, Antisymmetric (u.coreSlice s x))
    {E : ℝ} (hE : (E:EReal)≤unrestrictedFormBottom S) :
    E*mass u≤ sliceExpectation u (fun s x => form S (u.coreSlice s x).normalized) := by
  rw [←sliceExpectation_number u E]
  apply Finset.sum_le_sum
  intro s _
  apply integral_mono_ae
    (by simpa only [mul_comm (mass _) E] using (mass_coreSlice_integrable u s).const_mul E)
    (normalized_coreForm_weight_integrable S u s)
  filter_upwards [ha s] with x hx
  by_cases hz : mass (u.coreSlice s x)=0
  · simp [hz]
  · have hp := lt_of_le_of_ne (mass_nonneg (u.coreSlice s x)) (Ne.symm hz)
    apply mul_le_mul_of_nonneg_left _ hp.le
    exact EReal.coe_le_coe_iff.mp (hE.trans
      (unrestrictedFormBottom_le_trial S _ hx.normalized (mass_normalized _ hp)))

end Coulomb
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

lemma measurable_observationArrayPositions {H : Type*} {n : ℕ} (h : H) :
    Measurable (@observationArrayPositions H n h) := by
  unfold observationArrayPositions
  fun_prop

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
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_CoreCount
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma localCount_core_le {m k : ℕ} (A : Set Space) (x : Configuration (m+k))
    (hx : ∀ i : Fin k, position x (Fin.natAdd m i)∈A) : (k:ℝ)≤localCount A x := by
  unfold localCount
  rw [Fin.sum_univ_add]
  have he : (∑ i : Fin k, A.indicator (fun _ => (1:ℝ)) (position x (Fin.natAdd m i)))=k := by
    simp only [indicator_of_mem (hx _),Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  rw [he]
  exact le_add_of_nonneg_left (Finset.sum_nonneg (fun _ _ => indicator_nonneg (fun _ _ => zero_le_one) _))

lemma localCount_le_core {m k : ℕ} (A : Set Space) (x : Configuration (m+k))
    (hx : ∀ i : Fin m, position x (Fin.castAdd k i)∉A) : localCount A x≤(k:ℝ) := by
  unfold localCount
  rw [Fin.sum_univ_add]
  have he : (∑ i : Fin m, A.indicator (fun _ => (1:ℝ)) (position x (Fin.castAdd k i)))=0 := by
    simp only [indicator_of_notMem (hx _),Finset.sum_const_zero]
  rw [he,zero_add]
  calc
    _ ≤ ∑ _i : Fin k, (1:ℝ) := Finset.sum_le_sum (fun i _ => by
      by_cases h : position x (Fin.natAdd m i)∈A <;> simp [h])
    _ = _ := by simp

lemma PartlySupported.core_population {m k : ℕ} {v : H1Vector (m+k)}
    {A : Set Space} (hA : MeasurableSet A) (hv : PartlySupported v (coreIndexSet m k) A) :
    (k:ℝ)*mass v≤expectedPopulation v A := by
  rw [expectedPopulation_eq v hA]
  unfold mass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  rw [←integral_const_mul]
  apply integral_mono_ae (((v.value_L2 s).integrable_norm_pow (p:=2) (by norm_num)).const_mul _)
    (by simpa using localCount_weight_integrable v hA s 1)
  filter_upwards [hv s] with x hx
  by_cases hz : v.value s x=0
  · simp [hz]
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact localCount_core_le A x (fun i => by
      by_contra h
      exact hz (hx _ ⟨i,rfl⟩ h))

lemma positiveInnerDeficit_measurable {n : ℕ} (Z : ℝ) {A : Set Space} (hA : MeasurableSet A) :
    Measurable (positiveInnerDeficit (n:=n) Z A) :=
  (measurable_const.sub (localCount_measurable hA)).max measurable_const

lemma positiveInnerDeficit_nonneg {n : ℕ} (Z : ℝ) (A : Set Space) (x : Configuration n) :
    0≤positiveInnerDeficit Z A x := le_max_right _ _

lemma positiveInnerDeficit_le {n : ℕ} {Z : ℝ} (hZ : 0≤Z) (A : Set Space) (x : Configuration n) :
    positiveInnerDeficit Z A x≤Z := max_le (sub_le_self _ (localCount_nonneg _ _)) hZ

lemma PartlySupported.deficit_moment {m k : ℕ} {v : H1Vector (m+k)} {Z : ℝ} (hZ : 0≤Z)
    {A B : Set Space} (hA : MeasurableSet A) (hAB : Disjoint A B)
    (hv : PartlySupported v (outIndexSet m k) B) :
    (max (Z-(k:ℝ)) 0)^2*mass v≤potentialForm (fun x => (positiveInnerDeficit Z A x)^2) v := by
  unfold mass potentialForm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  rw [←integral_const_mul]
  apply integral_mono_ae (((v.value_L2 s).integrable_norm_pow (p:=2) (by norm_num)).const_mul _)
    (boundedObservable_integrable v _ ((positiveInnerDeficit_measurable Z hA).pow_const 2)
      (fun x => by
        rw [abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (positiveInnerDeficit_nonneg _ _ _) (positiveInnerDeficit_le hZ A x) 2) s)
  filter_upwards [hv s] with x hx
  by_cases hz : v.value s x=0
  · simp [hz]
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply pow_le_pow_left₀ (le_max_right _ _)
    apply max_le_max_right
    apply sub_le_sub_left
    exact localCount_le_core A x (fun i hi => by
      have hn : position x (Fin.castAdd k i)∉B := fun h => Set.disjoint_left.mp hAB hi h
      exact hz (hx _ ⟨i,rfl⟩ hn))

namespace RecordedEnsemble

lemma coreMean_le_population {n : ℕ} {T : RecordedEnsemble n} {ψ : H1Vector n}
    (hT : T.Conserves ψ) {A : Set Space} (hA : MeasurableSet A) (hs : T.CoreSupported A) :
    T.coreMean≤expectedPopulation ψ A := by
  rw [←hT.population hA]
  exact Finset.sum_le_sum (fun p _ => (hs p).core_population hA)

lemma coreDeficitMoment_le_raw {n : ℕ} {T : RecordedEnsemble n} {ψ : H1Vector n}
    (hT : T.Conserves ψ) {Z : ℝ} (hZ : 0≤Z) {A B : Set Space} (hA : MeasurableSet A)
    (hAB : Disjoint A B) (hs : T.OutSupported B) :
    T.coreDeficitMoment Z≤potentialForm (fun x => (positiveInnerDeficit Z A x)^2) ψ := by
  have H := hT (fun x => (positiveInnerDeficit Z A x)^2)
    ((positiveInnerDeficit_measurable Z hA).pow_const 2)
    ⟨Z^2,fun x => by rw [abs_of_nonneg (sq_nonneg _)]; exact
      pow_le_pow_left₀ (positiveInnerDeficit_nonneg _ _ _) (positiveInnerDeficit_le hZ A x) 2⟩
  have he p : (fun x => (positiveInnerDeficit (n:=n) Z A x)^2) ∘ reindexConfiguration (T.labels p)=
      (fun x => (positiveInnerDeficit Z A x)^2) := by
    funext x
    simp only [Function.comp_def,positiveInnerDeficit,localCount_reindex]
  simp only [he] at H
  rw [←H]
  exact Finset.sum_le_sum (fun p _ => (hs p).deficit_moment hZ hA hAB)

lemma favorableMass_of_core_moments {n : ℕ} (T : RecordedEnsemble n) {Z M : ℝ}
    (hM : 0<M) (hm : T.totalMass=1) (hmean : 1≤Z-T.coreMean) (hsecond : T.coreDeficitMoment Z≤M) :
    1/M≤T.favorableMass Z := by
  have H p : 2*M*(Z-(T.core p:ℝ))*mass (T.vector p)≤
      (max (Z-(T.core p:ℝ)) 0)^2*mass (T.vector p)+
      M^2*(if (T.core p:ℝ)<Z then mass (T.vector p) else 0) := by
    by_cases hp : (T.core p:ℝ)<Z
    · rw [ite_eq_left hp,max_eq_left (by linarith)]
      nlinarith [mul_nonneg (sq_nonneg (Z-(T.core p:ℝ)-M)) (mass_nonneg (T.vector p))]
    · rw [ite_eq_right hp,max_eq_right (by linarith)]
      simp only [zero_pow (by decide : 2≠0),zero_mul,mul_zero,add_zero]
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)) (mass_nonneg _)
  have HH := Finset.sum_le_sum (s:=Finset.univ) (fun p _ => H p)
  have he : (∑ p, 2*M*(Z-(T.core p:ℝ))*mass (T.vector p))=2*M*(Z*T.totalMass-T.coreMean) := by
    simp only [totalMass,coreMean,Finset.mul_sum,Finset.sum_sub_distrib,mul_sub,sub_mul]
    simp only [mul_assoc]
  rw [he,hm,mul_one] at HH
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at HH
  change 2*M*(Z-T.coreMean)≤T.coreDeficitMoment Z+M^2*T.favorableMass Z at HH
  apply (div_le_iff₀ hM).mpr
  apply (mul_le_mul_iff_left₀ hM).mp
  nlinarith [mul_le_mul_of_nonneg_left hmean (show 0≤2*M by positivity)]

end RecordedEnsemble
end Coulomb
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

lemma slice_core_form_ge_sector {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    (ha : ∀ s, ∀ᵐ x, Antisymmetric (u.coreSlice s x))
    {P : ℝ} (hP : (P:EReal)≤ sectorFormBottom S k) :
    P*mass u≤ sliceExpectation u (fun s x => form S (u.coreSlice s x).normalized) := by
  rw [←sliceExpectation_number u P]
  apply Finset.sum_le_sum
  intro s _
  apply integral_mono_ae
    (by simpa only [mul_comm (mass _) P] using (mass_coreSlice_integrable u s).const_mul P)
    (normalized_coreForm_weight_integrable S u s)
  filter_upwards [ha s] with x hx
  by_cases hz : mass (u.coreSlice s x)=0
  · simp [hz]
  · have hp := lt_of_le_of_ne (mass_nonneg (u.coreSlice s x)) (Ne.symm hz)
    apply mul_le_mul_of_nonneg_left _ hp.le
    exact EReal.coe_le_coe_iff.mp (hP.trans (sInf_le
      ⟨(u.coreSlice s x).normalized,hx.normalized,mass_normalized _ hp,rfl⟩))

end Coulomb

end
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_CoreGap
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
namespace Coulomb.RecordedEnsemble

lemma core_gap_lower {J n Z : ℕ} (S : Nuclei J) (T : RecordedEnsemble n)
    (hF : T.CoreFermionic) (hmono : Antitone (sectorFormBottom S))
    {E P : ℝ} (hE : (E:EReal)≤unrestrictedFormBottom S)
    (hP : (P:EReal)≤ sectorFormBottom S (Z-1)) :
    E*T.totalMass+(P-E)*T.favorableMass Z≤T.totalCoreForm S := by
  have H p : E*mass (T.vector p)+(P-E)*(if (T.core p:ℝ)<(Z:ℝ) then mass (T.vector p) else 0)≤
      sliceExpectation (T.vector p) (fun s x => form S ((T.vector p).coreSlice s x).normalized) := by
    by_cases hp : (T.core p:ℝ)<(Z:ℝ)
    · rw [ite_eq_left hp]
      have hk : T.core p≤Z-1 := by have := (Nat.cast_lt (α:=ℝ)).mp hp; omega
      have h := slice_core_form_ge_sector S (T.vector p) (fun s => (hF p).coreSlice s) (hP.trans (hmono hk))
      nlinarith
    · rw [ite_eq_right hp,mul_zero,add_zero]
      exact slice_core_form_ge_baseline S (T.vector p) (fun s => (hF p).coreSlice s) hE
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun p _ => H p)
  simpa only [Finset.sum_add_distrib,←Finset.mul_sum,totalMass,favorableMass,totalCoreForm] using hh

lemma predecessor_bound_of_core_budget {J n Z : ℕ} (S : Nuclei J) (T : RecordedEnsemble n)
    (hF : T.CoreFermionic) (hmono : Antitone (sectorFormBottom S))
    {E P M C : ℝ} (hE : (E:EReal)≤unrestrictedFormBottom S)
    (hP : (P:EReal)≤ sectorFormBottom S (Z-1)) (hEP : E≤P)
    (hM : 0<M) (hm : T.totalMass=1) (hmean : 1≤(Z:ℝ)-T.coreMean)
    (hsecond : T.coreDeficitMoment Z≤M) (henergy : T.totalCoreForm S≤E+C) :
    P≤E+M*C := by
  have H := core_gap_lower S T hF hmono hE hP
  rw [hm,mul_one] at H
  have hf := favorableMass_of_core_moments T hM hm hmean hsecond
  have hc := mul_le_mul_of_nonneg_left hf (sub_nonneg.mpr hEP)
  have hd : (P-E)/M≤C := by
    simp only [div_eq_mul_inv,one_mul] at hc
    rw [div_eq_mul_inv]
    linarith
  have hmC := (div_le_iff₀ hM).mp hd
  nlinarith

end Coulomb.RecordedEnsemble
end

end
section
section
open MeasureTheory Set Filter
open scoped BigOperators Classical
noncomputable section
namespace NeutralAtom

lemma event_count_upper {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) {F : Configuration n → ℝ} (hF : Measurable F)
    (hF0 : ∀ x, 0≤F x) (hF1 : ∀ x, F x≤1)
    {A : Set Position} (hA : MeasurableSet A) {T : ℝ}
    (hmatch : ∀ x, 0<F x → Coulomb.localCount A (flattenConfiguration n x)≤T)
    (hp : 0 < stateWeightedIntegral ψ F) :
    (stateWeightedIntegral ψ F)⁻¹*stateWeightedIntegral ψ
      (fun x => F x*Coulomb.localCount A (flattenConfiguration n x))≤T := by
  have hm : Measurable (fun x : Configuration n => Coulomb.localCount A (flattenConfiguration n x)) :=
    (Coulomb.localCount_measurable hA).comp (flattenConfiguration n).continuous.measurable
  have H := stateWeightedIntegral_mono_bounded hd
    (F:=fun x => F x*Coulomb.localCount A (flattenConfiguration n x))
    (G:=fun x => T*F x) (hF.mul hm) (measurable_const.mul hF)
    (C:=(n:ℝ)) (D:=|T|)
    (fun x => by
      rw [abs_of_nonneg (mul_nonneg (hF0 x) (Coulomb.localCount_nonneg A _))]
      exact (mul_le_of_le_one_left (Coulomb.localCount_nonneg A _) (hF1 x)).trans
        (Coulomb.localCount_le A _))
    (fun x => by
      rw [abs_mul,abs_of_nonneg (hF0 x)]
      exact mul_le_of_le_one_right (abs_nonneg _) (hF1 x))
    (fun x => by
      by_cases hx : F x=0
      · simp [hx]
      · have H := mul_le_mul_of_nonneg_left (hmatch x (lt_of_le_of_ne (hF0 x) (Ne.symm hx))) (hF0 x)
        simpa only [mul_comm] using H)
  rw [stateWeightedIntegral_const_mul] at H
  calc
    _ ≤ (stateWeightedIntegral ψ F)⁻¹*(T*stateWeightedIntegral ψ F) :=
      mul_le_mul_of_nonneg_left H (inv_nonneg.mpr hp.le)
    _ = T := by field_simp

theorem atomic_arrayEvent_deficit_upper {H : Type*} [Fintype H] {n : ℕ}
    (Z : ℕ) (hZ : 1≤Z) {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (hn : normSquared ψ=1)
    (hmin : ∀ (χ : Wavefunction n) (h : Gradient n), FormDomain χ h → normSquared χ=1 → energy Z ψ g≤energy Z χ h)
    {E D₀ : ℝ} (hE : (E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ))
    (hbase : energy Z ψ g≤E+D₀) (hD : 0≤D₀)
    (ℓ : H → ℝ) (hℓ : ∀ h, 0<ℓ h)
    {s : Set ((H × (Fin n × Fin 3)) → ℝ)} (hs : MeasurableSet s)
    (hsym : ∀ (p : Equiv.Perm (Fin n)) y, permuteObservationArray p y∈s ↔ y∈s)
    (hp : 0 < stateWeightedIntegral ψ (arrayEventLikelihood ℓ s)) {r T : ℝ} (hr : 0 < r)
    (hmatch : ∀ x, 0<arrayEventLikelihood ℓ s x →
      Coulomb.localCount (Metric.ball 0 r) (flattenConfiguration n x)≤(Z:ℝ)-T) :
    T≤2*Coulomb.atomicInnerFieldConstant*Coulomb.screenMass
      (D₀+observationEventEnergyConstant*observationWidthSquareSum ℓ*
        (1-Real.log (stateWeightedIntegral ψ (arrayEventLikelihood ℓ s)))^5) r := by
  obtain ⟨u,hu,hum,hue,hlaw⟩ := atomic_arrayEvent_state Z hZ hd hn hmin hbase ℓ hℓ hs hsym hp
  have hb := Coulomb.atomic_inner_deficit_upper (Coulomb.atom Z hZ) (by intro i; rfl)
    u hu hum hE hue (observationEventOffset_nonneg hd hn hD ℓ hs hp) hr
  rw [Coulomb.expectedPopulation_eq u measurableSet_ball] at hb
  change Coulomb.totalCharge (Coulomb.atom Z hZ)-Coulomb.potentialForm _ u≤_ at hb
  rw [hlaw] at hb
  have hlow := event_count_upper hd (arrayEventLikelihood_contDiff ℓ hs).continuous.measurable
    (arrayEventLikelihood_nonneg ℓ hs) (arrayEventLikelihood_le_one ℓ hs)
    measurableSet_ball hmatch hp
  have hcharge : Coulomb.totalCharge (Coulomb.atom Z hZ)=(Z:ℝ) := by
    simp [Coulomb.totalCharge,Coulomb.atom]
  rw [hcharge] at hb
  linarith

lemma raw_inner_observed_count_le {n : ℕ} (x y : Configuration n) {r a e : ℝ}
    (hre : r+e≤a) (hxy : ∀ i, ‖y i-x i‖≤e) :
    Coulomb.localCount (Metric.ball 0 r) (flattenConfiguration n x)≤
      rawCount (Metric.ball 0 a) y := by
  simp only [Coulomb.localCount,position_flattenConfiguration,rawCount]
  apply Finset.sum_le_sum
  intro i _
  by_cases hx : x i∈Metric.ball 0 r
  · have hx' : ‖x i‖ < r := by simpa only [Metric.mem_ball,dist_zero_right] using hx
    have hh : ‖y i‖≤‖y i-x i‖+‖x i‖ := by
      simpa only [sub_add_cancel] using norm_add_le (y i-x i) (x i)
    have hy : y i∈Metric.ball 0 a := by
      rw [Metric.mem_ball,dist_zero_right]
      linarith [hxy i]
    simp only [indicator_of_mem hx,indicator_of_mem hy,le_refl]
  · rw [indicator_of_notMem hx]
    exact indicator_nonneg (fun _ _ => by positivity) _

lemma observed_deficit_event_measurable {H : Type*} {n : ℕ} (h : H) (Z a T : ℝ) :
    MeasurableSet {y : (H × (Fin n × Fin 3)) → ℝ |
      T<Z-rawCount (Metric.ball 0 a) (observationArrayPositions h y)} :=
  measurableSet_lt measurable_const (measurable_const.sub
    ((measurable_rawCount measurableSet_ball).comp (measurable_observationArrayPositions h)))

lemma observed_deficit_event_symmetric {H : Type*} {n : ℕ} (h : H) (Z a T : ℝ)
    (p : Equiv.Perm (Fin n)) (y : (H × (Fin n × Fin 3)) → ℝ) :
    permuteObservationArray p y∈{y | T<Z-rawCount (Metric.ball 0 a) (observationArrayPositions h y)} ↔
    y∈{y | T<Z-rawCount (Metric.ball 0 a) (observationArrayPositions h y)} := by
  have he : observationArrayPositions h (permuteObservationArray p y)=observationArrayPositions h y ∘ p := rfl
  simp only [mem_ofPred_eq,he,rawCount,Function.comp_apply]
  have hh := Equiv.sum_comp p (fun i => (Metric.ball 0 a).indicator (fun _ => (1:ℝ)) (observationArrayPositions h y i))
  exact congrArg (fun q => T<Z-q) hh |> Iff.of_eq

theorem atomic_observed_inner_deficit_tail {H : Type*} [Fintype H] {n : ℕ}
    (Z : ℕ) (hZ : 1≤Z) {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (hn : normSquared ψ=1)
    (hmin : ∀ (χ : Wavefunction n) (h : Gradient n), FormDomain χ h → normSquared χ=1 → energy Z ψ g≤energy Z χ h)
    {E D₀ : ℝ} (hE : (E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ))
    (hbase : energy Z ψ g≤E+D₀) (hD : 0≤D₀)
    (ℓ : H → ℝ) (hℓ : ∀ h, 0<ℓ h) (h : H) {r a T p₀ : ℝ}
    (hr : 0 < r) (hp₀ : 0<p₀) (hre : r+Real.sqrt 3*ℓ h≤a)
    (hth : 2*Coulomb.atomicInnerFieldConstant*Coulomb.screenMass
      (D₀+observationEventEnergyConstant*observationWidthSquareSum ℓ*(1-Real.log p₀)^5) r<T) :
    stateWeightedIntegral ψ (arrayEventLikelihood ℓ
      {y | T<(Z:ℝ)-rawCount (Metric.ball 0 a) (observationArrayPositions h y)})≤p₀ := by
  let s : Set ((H × (Fin n × Fin 3)) → ℝ) :=
    {y | T<(Z:ℝ)-rawCount (Metric.ball 0 a) (observationArrayPositions h y)}
  have hs : MeasurableSet s := observed_deficit_event_measurable h Z a T
  by_contra hc
  have hp : 0 < stateWeightedIntegral ψ (arrayEventLikelihood ℓ s) := hp₀.trans (lt_of_not_ge hc)
  have hp1 := stateWeightedIntegral_le_one hd hn (arrayEventLikelihood_contDiff ℓ hs).continuous.measurable
    (arrayEventLikelihood_nonneg ℓ hs) (arrayEventLikelihood_le_one ℓ hs)
  have hm : ∀ x, 0<arrayEventLikelihood ℓ s x →
      Coulomb.localCount (Metric.ball 0 r) (flattenConfiguration n x)≤(Z:ℝ)-T := by
    intro x hx
    obtain ⟨u,hu,he⟩ := arrayEventLikelihood_pos_matching ℓ (fun k => (hℓ k).ne') s x hx
    have H := raw_inner_observed_count_le x
      (observationArrayPositions h (fun ia => x ia.2.1 ia.2.2+ℓ ia.1*u ia)) hre
      (observationArrayPositions_displacement ℓ hℓ x hu h)
    change T<(Z:ℝ)-rawCount _ _ at he
    linarith
  have hb := atomic_arrayEvent_deficit_upper Z hZ hd hn hmin hE hbase hD ℓ hℓ hs
    (observed_deficit_event_symmetric h Z a T) hp hr hm
  have hδ := observationEventOffset_mono_probability ℓ D₀ hp₀ (le_of_not_ge hc) hp1
  have hmass : Coulomb.screenMass (D₀+observationEventEnergyConstant*observationWidthSquareSum ℓ*
      (1-Real.log (stateWeightedIntegral ψ (arrayEventLikelihood ℓ s)))^5) r≤
    Coulomb.screenMass (D₀+observationEventEnergyConstant*observationWidthSquareSum ℓ*(1-Real.log p₀)^5) r := by
    unfold Coulomb.screenMass
    exact add_le_add le_rfl (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hδ hr.le))
  have := mul_le_mul_of_nonneg_left hmass
    (mul_nonneg (by norm_num : (0:ℝ)≤2) Coulomb.atomicInnerFieldConstant_nonneg)
  linarith

end NeutralAtom

end

end
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
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace NeutralAtom

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

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ObservedUnordered
attribute [-instance] _root_.OAI.NeutralAtom.observationNoiseLaw_negInvariant _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace NeutralAtom

lemma observationNoiseLaw_ae_support : ∀ᵐ u ∂observationNoiseLaw, |u|<1 := by
  rw [observationNoiseLaw,ae_withDensity_iff observationNoiseDensity_contDiff.continuous.measurable.ennreal_ofReal]
  filter_upwards [] with u hu
  by_contra hn
  apply hu
  simp [observationNoiseDensity_formula,hn]

lemma allObservationNoiseLaw_ae_support (n J : ℕ) :
    ∀ᵐ u ∂allObservationNoiseLaw n J, ∀ j i a, |u j i a|<1 := by
  simp only [ae_all_iff]
  intro j i a
  exact ((measurePreserving_eval (fun _ : Fin 3 => observationNoiseLaw) a).comp
    ((measurePreserving_eval (fun _ : Fin n => Measure.pi (fun _ : Fin 3 => observationNoiseLaw)) i).comp
      (measurePreserving_eval (fun _ : Fin J => Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin 3 => observationNoiseLaw))) j))).quasiMeasurePreserving.ae observationNoiseLaw_ae_support

lemma observationNoiseVector_norm_le {v : Fin 3 → ℝ} (hv : ∀ a, |v a|≤1) :
    ‖observationNoiseVector v‖≤Real.sqrt 3 := by
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq,Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  calc
    _≤∑ _a : Fin 3, (1:ℝ) := Finset.sum_le_sum (fun a _ => by
      rw [observationNoiseVector_coordinate]
      nlinarith [(abs_le.mp (hv a)).1,(abs_le.mp (hv a)).2])
    _=_ := by norm_num

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PhysicalDeficitTail
attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators Classical
noncomputable section
namespace NeutralAtom

theorem physical_observed_inner_deficit_tail {n J : ℕ}
    (Z : ℕ) (hZ : 1≤Z) {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (hn : normSquared ψ=1)
    (hmin : ∀ (χ : Wavefunction n) (h : Gradient n), FormDomain χ h → normSquared χ=1 → energy Z ψ g≤energy Z χ h)
    {E D₀ : ℝ} (hE : (E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ))
    (hbase : energy Z ψ g≤E+D₀) (hD : 0≤D₀)
    (ℓ : Fin J → ℝ) (hℓ : ∀ h, 0<ℓ h) (h : Fin J) {r a T p₀ : ℝ}
    (hr : 0 < r) (hp₀ : 0<p₀) (hre : r+Real.sqrt 3*ℓ h≤a)
    (hth : 2*Coulomb.atomicInnerFieldConstant*Coulomb.screenMass
      (D₀+observationEventEnergyConstant*observationWidthSquareSum ℓ*(1-Real.log p₀)^5) r<T) :
    (observationLaw J (rawLaw ψ)).real
      (observationCoordinateData ℓ ⁻¹'
        {y | T<(Z:ℝ)-rawCount (Metric.ball 0 a) (observationArrayPositions h y)})≤p₀ := by
  rw [physical_arrayEvent_probability hd.2.2.1 hn ℓ (fun h => (hℓ h).ne')
    (observed_deficit_event_measurable h Z a T)]
  exact atomic_observed_inner_deficit_tail Z hZ hd hn hmin hE hbase hD ℓ hℓ h hr hp₀ hre hth

lemma deficit_screening_exponential_cutoff {B K D r k : ℝ}
    (hB : 0≤B) (hK : 0≤K) (hD : 0≤D) (hr : 0 ≤ r) (hk : 0≤k) :
    B*Coulomb.screenMass (D+K*(1-Real.log (Real.exp (-k)))^5) r <
      (B*(Coulomb.screenBaseMass r+Real.sqrt ((D+K)*r))+1)*(1+k)^3 := by
  rw [Real.log_exp]
  have hv : 1≤1+k := by linarith
  have h6 : 1≤(1+k)^6 := one_le_pow₀ hv
  have h56 : (1+k)^5≤(1+k)^6 := by
    calc
      _ ≤ (1+k)^5*(1+k) := le_mul_of_one_le_right (by positivity) hv
      _ = _ := by ring
  have hδ : (D+K*(1- -k)^5)*r≤((D+K)*r)*((1+k)^3)^2 := by
    have hD' := mul_le_mul_of_nonneg_left h6 hD
    have hK' := mul_le_mul_of_nonneg_left h56 hK
    have H : D+K*(1- -k)^5≤(D+K)*(1+k)^6 := by nlinarith
    have H' := mul_le_mul_of_nonneg_right H hr
    nlinarith
  have hs : Real.sqrt ((D+K*(1- -k)^5)*r)≤Real.sqrt ((D+K)*r)*(1+k)^3 := by
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity,?_⟩
    rw [mul_pow,Real.sq_sqrt (mul_nonneg (add_nonneg hD hK) hr)]
    exact hδ
  have hbase : Coulomb.screenBaseMass r≤Coulomb.screenBaseMass r*(1+k)^3 :=
    le_mul_of_one_le_right (Coulomb.screenBaseMass_nonneg r) (one_le_pow₀ hv)
  unfold Coulomb.screenMass
  have H := mul_le_mul_of_nonneg_left (add_le_add hbase hs) hB
  have hp : 0<(1+k)^3 := by positivity
  nlinarith

theorem physical_observed_deficit_exponential_tail {n J : ℕ}
    (Z : ℕ) (hZ : 1≤Z) {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (hn : normSquared ψ=1)
    (hmin : ∀ (χ : Wavefunction n) (h : Gradient n), FormDomain χ h → normSquared χ=1 → energy Z ψ g≤energy Z χ h)
    {E D₀ : ℝ} (hE : (E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ))
    (hbase : energy Z ψ g≤E+D₀) (hD : 0≤D₀)
    (ℓ : Fin J → ℝ) (hℓ : ∀ h, 0<ℓ h) (h : Fin J) {r a k : ℝ}
    (hr : 0 < r) (hk : 0≤k) (hre : r+Real.sqrt 3*ℓ h≤a) :
    (observationLaw J (rawLaw ψ)).real
      (observationCoordinateData ℓ ⁻¹'
        {y | observedDeficitCoefficient ℓ D₀ r*(1+k)^3<
          (Z:ℝ)-rawCount (Metric.ball 0 a) (observationArrayPositions h y)})≤Real.exp (-k) := by
  exact physical_observed_inner_deficit_tail Z hZ hd hn hmin hE hbase hD ℓ hℓ h hr
    (Real.exp_pos _) hre (deficit_screening_exponential_cutoff
      (mul_nonneg (by norm_num) Coulomb.atomicInnerFieldConstant_nonneg)
      (mul_nonneg observationEventEnergyConstant_pos.le (observationWidthSquareSum_nonneg ℓ)) hD hr.le hk)
end NeutralAtom

end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_DeficitMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators Classical
noncomputable section
namespace NeutralAtom

lemma sq_le_discrete_tail_sum (t : ℕ → ℝ) (_ht : ∀ k, 0≤t k)
    {x : ℝ} (hx : 0≤x) (N : ℕ) (hxN : x≤t N) :
    x^2≤(t 0)^2+∑ k∈Finset.range N, (t (k+1))^2*(if t k<x then 1 else 0) := by
  induction N with
  | zero => simpa using pow_le_pow_left₀ hx hxN 2
  | succ N ih =>
    rw [Finset.sum_range_succ]
    by_cases H : x≤t N
    · have hn : 0≤(t (N+1))^2*(if t N<x then 1 else 0) := by split_ifs <;> positivity
      linarith [ih H]
    · rw [ite_eq_left (lt_of_not_ge H),mul_one]
      have hsum : 0≤∑ k∈Finset.range N, (t (k+1))^2*(if t k<x then 1 else 0) := by
        apply Finset.sum_nonneg
        intro k _
        split_ifs <;> positivity
      have hpow := pow_le_pow_left₀ hx hxN 2
      nlinarith [sq_nonneg (t 0)]

theorem secondMoment_le_discrete_tails {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    (hf0 : ∀ ω, 0≤f ω) (t b : ℕ → ℝ) (ht : ∀ k, 0≤t k)
    (N : ℕ) (hbound : ∀ ω, f ω≤t N)
    (htail : ∀ k, μ.real {ω | t k<f ω}≤b k)
    (hsum : Summable (fun k => (t (k+1))^2*b k)) :
    (∫ ω, (f ω)^2 ∂μ)≤(t 0)^2+∑' k, (t (k+1))^2*b k := by
  let F : ℕ → Ω → ℝ := fun k => ({ω | t k<f ω}).indicator (fun _ => (1:ℝ))
  have hF : ∀ k, Integrable (F k) μ := fun k =>
    (integrable_const 1).indicator (measurableSet_lt measurable_const hf)
  have hfi : Integrable (fun ω => (f ω)^2) μ := by
    apply (integrable_const ((t N)^2)).mono' (hf.pow_const 2).aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (hf0 ω) (hbound ω) 2
  have hgi : Integrable (fun ω => (t 0)^2+∑ k∈Finset.range N, (t (k+1))^2*F k ω) μ :=
    (integrable_const _).add (integrable_finsetSum _ (fun k _ => (hF k).const_mul _))
  have H := integral_mono hfi hgi (fun ω => sq_le_discrete_tail_sum t ht (hf0 ω) N (hbound ω))
  have hInt : (∫ ω, (t 0)^2+∑ k∈Finset.range N, (t (k+1))^2*F k ω ∂μ)=
      (t 0)^2+∑ k∈Finset.range N, (t (k+1))^2*μ.real {ω | t k<f ω} := by
    rw [integral_add (integrable_const _) (integrable_finsetSum _ (fun k _ => (hF k).const_mul _)),
      integral_finsetSum _ (fun k _ => (hF k).const_mul _)]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_const_mul]
    congr 1
    exact integral_indicator_const _ (measurableSet_lt measurable_const hf) |>.trans (by simp)
  rw [hInt] at H
  apply H.trans
  exact add_le_add le_rfl (by
    calc
      _ ≤ ∑ k∈Finset.range N, (t (k+1))^2*b k :=
        Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (htail k) (sq_nonneg _))
      _ ≤ ∑' k, (t (k+1))^2*b k :=
        hsum.sum_le_tsum _ (fun k _ => mul_nonneg (sq_nonneg _) ((measureReal_nonneg).trans (htail k)))
  )

lemma summable_cubic_exponential_tail (C : ℝ) :
    Summable (fun k : ℕ => (C*(1+((k+1:ℕ):ℝ))^3)^2*Real.exp (-(k:ℝ))) := by
  have hs := Real.summable_pow_mul_exp_neg_nat_mul 6 (r:=1) (by norm_num)
  have hshift := (summable_nat_add_iff 2).mpr hs
  have hsimple : Summable (fun k : ℕ => ((k:ℝ)+2)^6*Real.exp (-((k:ℝ)+2))) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,neg_mul,one_mul] using hshift
  have heq : (fun k : ℕ => (C*(1+((k+1:ℕ):ℝ))^3)^2*Real.exp (-(k:ℝ))) =
      (fun k : ℕ => (C^2*Real.exp 2)*(((k:ℝ)+2)^6*Real.exp (-((k:ℝ)+2)))) := by
    funext k
    have he : Real.exp 2*Real.exp (-((k:ℝ)+2))=Real.exp (-(k:ℝ)) := by
      rw [←Real.exp_add]
      congr 1
      ring
    simp only [Nat.cast_add,Nat.cast_one]
    calc
      _ = C^2*((k:ℝ)+2)^6*(Real.exp 2*Real.exp (-((k:ℝ)+2))) := by rw [he]; ring
      _ = _ := by ring
  rw [heq]
  exact hsimple.mul_left (C^2*Real.exp 2)

end NeutralAtom

end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PhysicalDeficitMoment
attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators Classical
noncomputable section
namespace NeutralAtom

theorem physical_observed_positive_deficit_second_moment {n J : ℕ}
    (Z : ℕ) (hZ : 1≤Z) {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (hn : normSquared ψ=1)
    (hmin : ∀ (χ : Wavefunction n) (h : Gradient n), FormDomain χ h → normSquared χ=1 → energy Z ψ g≤energy Z χ h)
    {E D₀ : ℝ} (hE : (E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ))
    (hbase : energy Z ψ g≤E+D₀) (hD : 0≤D₀)
    (ℓ : Fin J → ℝ) (hℓ : ∀ h, 0<ℓ h) (h : Fin J) {r a : ℝ}
    (hr : 0 < r) (hre : r+Real.sqrt 3*ℓ h≤a) :
    (∫ sample, (max ((Z:ℝ)-rawCount (Metric.ball 0 a)
      (observationArrayPositions h (observationCoordinateData ℓ sample))) 0)^2
      ∂observationLaw J (rawLaw ψ))≤
      (observedDeficitCoefficient ℓ D₀ r)^2+
        ∑' k : ℕ, (observedDeficitCoefficient ℓ D₀ r*(1+((k+1:ℕ):ℝ))^3)^2*Real.exp (-(k:ℝ)) := by
  have := rawLaw_isProbability hd.2.2.1 hn
  let C := observedDeficitCoefficient ℓ D₀ r
  let f : ObservationSample n J → ℝ := fun sample =>
    max ((Z:ℝ)-rawCount (Metric.ball 0 a)
      (observationArrayPositions h (observationCoordinateData ℓ sample))) 0
  let t : ℕ → ℝ := fun k => C*(1+(k:ℝ))^3
  have hC : 1≤C := by
    dsimp [C,observedDeficitCoefficient]
    have : 0≤2*Coulomb.atomicInnerFieldConstant*(Coulomb.screenBaseMass r+
      Real.sqrt ((D₀+observationEventEnergyConstant*observationWidthSquareSum ℓ)*r)) :=
      mul_nonneg (mul_nonneg (by norm_num) Coulomb.atomicInnerFieldConstant_nonneg)
        (add_nonneg (Coulomb.screenBaseMass_nonneg r) (Real.sqrt_nonneg _))
    linarith
  have ht : ∀ k, 0≤t k := fun k => mul_nonneg (by linarith) (by positivity)
  have hf : Measurable f :=
    (measurable_const.sub ((measurable_rawCount measurableSet_ball).comp
      ((measurable_observationArrayPositions h).comp (measurable_observationCoordinateData ℓ)))).max measurable_const
  have hz : 0≤(Z:ℝ) := Nat.cast_nonneg _
  have hb : ∀ sample, f sample≤t Z := by
    intro sample
    have hfZ : f sample≤(Z:ℝ) := max_le
      (sub_le_self _ (rawCount_nonneg _ _)) hz
    have hp : (Z:ℝ)≤(1+(Z:ℝ))^3 := by nlinarith [sq_nonneg (Z:ℝ),pow_nonneg hz 3]
    exact hfZ.trans (hp.trans (le_mul_of_one_le_left (by positivity) hC))
  have htail : ∀ k, (observationLaw J (rawLaw ψ)).real {sample | t k<f sample}≤Real.exp (-(k:ℝ)) := by
    intro k
    have he : {sample | t k<f sample}=observationCoordinateData ℓ ⁻¹'
        {y | C*(1+(k:ℝ))^3<(Z:ℝ)-rawCount (Metric.ball 0 a) (observationArrayPositions h y)} := by
      ext sample
      simp only [f,t,mem_preimage,mem_ofPred_eq,lt_max_iff,not_lt.mpr (ht k),or_false]
    rw [he]
    exact physical_observed_deficit_exponential_tail Z hZ hd hn hmin hE hbase hD ℓ hℓ h hr
      (Nat.cast_nonneg k) hre
  have H := secondMoment_le_discrete_tails (observationLaw J (rawLaw ψ)) hf
    (fun sample => le_max_right _ _) t (fun k => Real.exp (-(k:ℝ))) ht Z hb htail
    (summable_cubic_exponential_tail C)
  simpa only [f,t,Nat.cast_zero,add_zero,one_pow,mul_one] using H
end NeutralAtom
end

end
end
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace NeutralAtom

lemma observationCoordinateData_positions_linear {n J : ℕ} (ℓ : Fin J → ℝ)
    (sample : ObservationSample n J) (j : Fin J) (i : Fin n) :
    observationArrayPositions j (observationCoordinateData ℓ sample) i =
      sample.1 i+ℓ j • observationNoiseVector (sample.2 j i) := by
  ext a
  simp [observationArrayPositions,observationCoordinateData,observationNoiseVector_coordinate]

lemma observationLaw_ae_linear_displacement {n J : ℕ} (ν : Measure (Configuration n))
    [IsProbabilityMeasure ν] (ℓ : Fin J → ℝ) (hℓ : ∀ j, 0≤ℓ j) :
    ∀ᵐ sample ∂observationLaw J ν, ∀ j i,
      ‖observationArrayPositions j (observationCoordinateData ℓ sample) i-sample.1 i‖≤
        Real.sqrt 3*ℓ j := by
  have hh : ∀ᵐ z ∂observationLaw J ν, ∀ j i a, |z.2 j i a|<1 :=
    measurePreserving_snd.quasiMeasurePreserving.ae (allObservationNoiseLaw_ae_support n J)
  filter_upwards [hh] with z hz j i
  rw [observationCoordinateData_positions_linear,add_sub_cancel_left,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (hℓ j)]
  exact (mul_le_mul_of_nonneg_left (observationNoiseVector_norm_le (fun a => (hz j i a).le))
    (hℓ j)).trans_eq (mul_comm _ _)

lemma rawCount_flatten {n : ℕ} (A : Set Position) (x : Configuration n) :
    Coulomb.localCount A (flattenConfiguration n x)=rawCount A x := by
  simp only [Coulomb.localCount,rawCount,position_flattenConfiguration]

lemma raw_positive_deficit_moment_le_observed {n J : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hn : normSquared ψ=1)
    {Z : ℝ} (hZ : 0≤Z) (ℓ : Fin J → ℝ) (hℓ : ∀ j, 0≤ℓ j)
    (j : Fin J) {a t : ℝ} (hat : a+Real.sqrt 3*ℓ j≤t) :
    stateWeightedIntegral ψ (fun x => (max (Z-rawCount (Metric.ball 0 t) x) 0)^2) ≤
      ∫ sample, (max (Z-rawCount (Metric.ball 0 a)
        (observationArrayPositions j (observationCoordinateData ℓ sample))) 0)^2
        ∂observationLaw J (rawLaw ψ) := by
  let := rawLaw_isProbability hψ hn
  let f : Configuration n → ℝ := fun x => (max (Z-rawCount (Metric.ball 0 t) x) 0)^2
  let g : ObservationSample n J → ℝ := fun sample =>
    (max (Z-rawCount (Metric.ball 0 a)
      (observationArrayPositions j (observationCoordinateData ℓ sample))) 0)^2
  have hb (A : Set Position) (x : Configuration n) : ‖(max (Z-rawCount A x) 0)^2‖≤Z^2 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (le_max_right _ _) (max_le (sub_le_self _ (rawCount_nonneg _ _)) hZ) 2
  have hf : Measurable f := ((measurable_const.sub (measurable_rawCount measurableSet_ball)).max measurable_const).pow_const 2
  have hg : Measurable g := ((measurable_const.sub ((measurable_rawCount measurableSet_ball).comp
    ((measurable_observationArrayPositions j).comp (measurable_observationCoordinateData ℓ)))).max measurable_const).pow_const 2
  have hi : Integrable (fun z : ObservationSample n J => f z.1) (observationLaw J (rawLaw ψ)) :=
    (integrable_const (Z^2)).mono' (hf.comp measurable_fst).aestronglyMeasurable
      (Eventually.of_forall (fun z => hb _ z.1))
  have hgi : Integrable g (observationLaw J (rawLaw ψ)) :=
    (integrable_const (Z^2)).mono' hg.aestronglyMeasurable
      (Eventually.of_forall (fun z => hb _ _))
  have he : (∫ z : ObservationSample n J, f z.1 ∂observationLaw J (rawLaw ψ))=
      stateWeightedIntegral ψ f := by
    rw [observationLaw,integral_prod _ hi]
    simp only [integral_const,probReal_univ,one_smul]
    rw [integral_rawLaw hψ,rawExpectation_eq_stateWeightedIntegral hψ hf (fun x => hb _ x)]
  rw [←he]
  apply integral_mono_ae hi hgi
  filter_upwards [observationLaw_ae_linear_displacement (rawLaw ψ) ℓ hℓ] with sample hs
  dsimp [f,g]
  apply pow_le_pow_left₀ (le_max_right _ _)
  apply max_le_max_right
  apply sub_le_sub_left
  have H := raw_inner_observed_count_le
    (observationArrayPositions j (observationCoordinateData ℓ sample)) sample.1 hat
    (fun i => by simpa only [norm_sub_rev] using hs j i)
  simpa only [rawCount_flatten] using H

theorem physical_raw_positive_deficit_second_moment {n J : ℕ}
    (Z : ℕ) (hZ : 1≤Z) {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (hn : normSquared ψ=1)
    (hmin : ∀ (χ : Wavefunction n) (h : Gradient n), FormDomain χ h → normSquared χ=1 → energy Z ψ g≤energy Z χ h)
    {E D₀ : ℝ} (hE : (E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ))
    (hbase : energy Z ψ g≤E+D₀) (hD : 0≤D₀)
    (ℓ : Fin J → ℝ) (hℓ : ∀ h, 0<ℓ h) (j : Fin J) {r a t : ℝ}
    (hr : 0 < r) (hre : r+Real.sqrt 3*ℓ j≤a) (hat : a+Real.sqrt 3*ℓ j≤t) :
    Coulomb.potentialForm (fun x => (Coulomb.positiveInnerDeficit (Z:ℝ) (Metric.ball 0 t) x)^2)
      (asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1) ≤
      (observedDeficitCoefficient ℓ D₀ r)^2+
        ∑' k : ℕ, (observedDeficitCoefficient ℓ D₀ r*(1+((k+1:ℕ):ℝ))^3)^2*Real.exp (-(k:ℝ)) := by
  rw [asH1_potentialForm]
  simp only [Coulomb.positiveInnerDeficit,rawCount_flatten]
  exact (raw_positive_deficit_moment_le_observed hd.2.2.1 hn (Nat.cast_nonneg Z) ℓ
    (fun j => (hℓ j).le) j hat).trans
    (physical_observed_positive_deficit_second_moment Z hZ hd hn hmin hE hbase hD ℓ hℓ j hr hre)

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_CoreMoment
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

lemma fixedCoreMomentBound_pos (t : ℝ) : 0<fixedCoreMomentBound t := by
  unfold fixedCoreMomentBound
  have hs : 0≤∑' k : ℕ, (observedDeficitCoefficient (fun _ : Fin 1 => t/16) 0 (t/4)*
      (1+((k+1:ℕ):ℝ))^3)^2*Real.exp (-(k:ℝ)) :=
    tsum_nonneg (fun _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  positivity

lemma zero_offset_raw_deficit_moment {n : ℕ} (Z : ℕ) (hZ : 1≤Z)
    (u : Coulomb.H1Vector n) (ha : Coulomb.Antisymmetric u) (hm : Coulomb.mass u=1)
    {E : ℝ} (hE : (E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ))
    (he : Coulomb.form (Coulomb.atom Z hZ) u≤E) {t : ℝ} (ht : 0<t) :
    Coulomb.potentialForm (fun x => (Coulomb.positiveInnerDeficit (Z:ℝ) (Metric.ball 0 t) x)^2) u≤
      fixedCoreMomentBound t := by
  let ψ := fromH1Wave u
  let g := fromH1Gradient u
  have hd : FormDomain ψ g := fromH1_domain u ha
  have hn : normSquared ψ=1 := (fromH1_mass u).trans hm
  have hmin : ∀ (χ : Wavefunction n) (h : Gradient n), FormDomain χ h → normSquared χ=1 →
      energy Z ψ g≤energy Z χ h := by
    intro χ h hχ hχm
    have hv := Coulomb.unrestrictedFormBottom_le_trial (Coulomb.atom Z hZ)
      (asH1 χ h hχ.2.1 hχ.2.2.1 hχ.2.2.2.1) (asH1_antisymmetric hχ) ((asH1_mass ..).trans hχm)
    rw [asH1_energy Z hZ] at hv
    rw [fromH1_energy Z hZ]
    exact he.trans (EReal.coe_le_coe_iff.mp (hE.trans hv))
  have hbase : energy Z ψ g≤E+0 := by
    change energy Z (fromH1Wave u) (fromH1Gradient u)≤E+0
    simpa only [fromH1_energy Z hZ,add_zero] using he
  have hsqrt : Real.sqrt 3≤2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sqrt_nonneg 3]
  have hw : Real.sqrt 3*(t/16)≤t/8 := by nlinarith
  have H := physical_raw_positive_deficit_second_moment Z hZ hd hn hmin hE hbase le_rfl
    (fun _ : Fin 1 => t/16) (fun _ => by positivity) (0:Fin 1)
    (show 0<t/4 by positivity) (show t/4+Real.sqrt 3*(t/16)≤t/2 by linarith)
    (show t/2+Real.sqrt 3*(t/16)≤t by linarith)
  have H' : Coulomb.potentialForm (fun x => (Coulomb.positiveInnerDeficit (Z:ℝ) (Metric.ball 0 t) x)^2) u≤
      (observedDeficitCoefficient (fun _ : Fin 1 => t/16) 0 (t/4))^2+
        ∑' k : ℕ, (observedDeficitCoefficient (fun _ : Fin 1 => t/16) 0 (t/4)*
          (1+((k+1:ℕ):ℝ))^3)^2*Real.exp (-(k:ℝ)) := by
    simpa only [Coulomb.potentialForm,ψ,g,asH1,fromH1Wave,ContinuousLinearEquiv.apply_symm_apply] using H
  unfold fixedCoreMomentBound
  linarith

end NeutralAtom
namespace Coulomb.RecordedEnsemble

lemma zero_offset_core_deficit_moment {n : ℕ} (Z : ℕ) (hZ : 1≤Z)
    (u : H1Vector n) (ha : Antisymmetric u) (hm : mass u=1)
    {E : ℝ} (hE : (E:EReal)≤unrestrictedFormBottom (atom Z hZ))
    (he : form (atom Z hZ) u≤E) {t : ℝ} (ht : 0<t) (T : RecordedEnsemble n)
    (hT : T.Conserves u) (hO : T.OutSupported {y | t≤‖y‖}) :
    T.coreDeficitMoment Z≤NeutralAtom.fixedCoreMomentBound t := by
  have hd : Disjoint (Metric.ball (0:Space) t) {y | t≤‖y‖} := by
    refine Set.disjoint_left.mpr ?_
    intro y hy hz
    have : ‖y‖<t := by simpa only [Metric.mem_ball,dist_zero_right] using hy
    exact not_lt_of_ge hz this
  exact (coreDeficitMoment_le_raw hT (Nat.cast_nonneg Z) measurableSet_ball hd hO).trans
    (NeutralAtom.zero_offset_raw_deficit_moment Z hZ u ha hm hE he ht)

end Coulomb.RecordedEnsemble
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_SpectralTheory_CorePredecessor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

theorem atomic_predecessor_from_physical_mean_oai : ∃ C : ℝ, 0≤C ∧
    ∀ (Z : ℕ) (hZ : 1≤Z) {n : ℕ} (u : H1Vector n),
    Antisymmetric u → mass u=1 →
    ∀ {E : ℝ}, (E:EReal)≤unrestrictedFormBottom (atom Z hZ) → form (atom Z hZ) u≤E →
    ∀ {t : ℝ}, 0<t → expectedPopulation u (Metric.ball 0 (2*t))≤(Z:ℝ)-1 →
    (sectorFormBottom (atom Z hZ) (Z-1)).toReal≤
      E+NeutralAtom.fixedCoreMomentBound t*C*((screenMass 0 (t/4))^2/t+screenMass 0 t/t^2) := by
  obtain ⟨C,hC,HC⟩ := RecordedEnsemble.atomic_zero_offset_core_deletion
  refine ⟨C,hC,?_⟩
  intro Z hZ n u ha hm E hE he t ht hmean
  obtain ⟨T,hT,hF,hS,hO,hM,hform⟩ := HC (atom Z hZ) (fun _ => rfl) u ha hm hE he ht
  have hs : T.CoreSupported (Metric.ball 0 (2*t)) := by
    simpa only [Metric.ball,dist_zero_right] using hS
  have hm' : 1≤(Z:ℝ)-T.coreMean := by
    have hp := RecordedEnsemble.coreMean_le_population hT measurableSet_ball hs
    linarith
  have hsecond := RecordedEnsemble.zero_offset_core_deficit_moment Z hZ u ha hm hE he ht T hT hO
  let P := (sectorFormBottom (atom Z hZ) (Z-1)).toReal
  have hP : (P:EReal)=sectorFormBottom (atom Z hZ) (Z-1) := atom_sectorFormBottom_real Z hZ _
  have hEP : E≤P := EReal.coe_le_coe_iff.mp (hE.trans (by
    rw [hP]
    exact iInf_le (fun k => sectorFormBottom (atom Z hZ) k) (Z-1)))
  have H := T.predecessor_bound_of_core_budget (atom Z hZ) hF
    (atom_sectorFormBottom_antitone Z hZ) hE hP.le hEP
    (NeutralAtom.fixedCoreMomentBound_pos t) hM hm' hsecond hform
  simpa only [mul_assoc] using H

end Coulomb
end

end

end OAI
end

theorem solution : type_of% @OAI.Coulomb.atomic_predecessor_from_physical_mean_oai := @OAI.Coulomb.atomic_predecessor_from_physical_mean_oai
