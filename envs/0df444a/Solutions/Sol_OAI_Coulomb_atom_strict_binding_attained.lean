-- Prove2me | solution 1 for OAI.Coulomb.atom_strict_binding_attained
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:19:03.825728+00:00
-- url     : https://prove2.me/submissions/dbe7001e-7205-43ba-a420-9aa77c265e43

import Mathlib
import Definitions.Def_CoulombRadii
import Definitions.Def_OAIQ062C007
import Theorems.Thm_OAI_Coulomb_strictly_bound_sequence_tight

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_Add
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open ContinuousLinearMap
open scoped Convolution

lemma kinetic_nonneg {n : ℕ} (ψ : H1Vector n) : 0 ≤ kinetic ψ := by
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
    (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)))

lemma pairEnergy_nonneg {n : ℕ} (ψ : H1Vector n) : 0 ≤ pairEnergy ψ := by
  apply Finset.sum_nonneg
  intro s _
  apply integral_nonneg
  intro x
  apply mul_nonneg _ (sq_nonneg _)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact inv_nonneg.mpr (norm_nonneg _)
  · exact le_rfl

lemma totalCharge_ge_card {M : ℕ} (S : Nuclei M) : (M : ℝ) ≤ totalCharge S := by
  calc
    (M : ℝ) = ∑ _j : Fin M, (1 : ℝ) := by simp
    _ ≤ totalCharge S := Finset.sum_le_sum (fun j _ => S.charge_ge_one j)

lemma totalCharge_pos {M : ℕ} (S : Nuclei M) : 0 < totalCharge S :=
  (Nat.cast_pos.mpr S.nonempty).trans_le (totalCharge_ge_card S)

lemma nuclearEnergy_eq_sum {M n : ℕ} (S : Nuclei M) (ψ : H1Vector n) :
    nuclearEnergy S ψ = ∑ s, ∑ i, ∑ j,
      S.charge j * (∫ x, coulombKernel (position x i - S.position j) * ‖ψ.value s x‖^2) := by
  unfold nuclearEnergy
  apply Finset.sum_congr rfl
  intro s _
  have hI : ∀ i j, Integrable (fun x => S.charge j *
      (coulombKernel (position x i - S.position j) * ‖ψ.value s x‖^2)) := by
    intro i j
    exact ((ψ.nuclear_coulomb_integrable_bound s i (S.position j)
      (by norm_num : (0 : ℝ) < 1)).1).const_mul _
  simp only [attraction, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hI i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hI i j)]
  simp only [integral_const_mul]

lemma nuclearEnergy_bound {M n : ℕ} (S : Nuclei M) (ψ : H1Vector n)
    {η : ℝ} (hη : 0 < η) :
    nuclearEnergy S ψ ≤ 8 * η * totalCharge S * kinetic ψ +
      ((n : ℝ) * totalCharge S / (4 * η)) * mass ψ := by
  let K : Spins n → Fin n → ℝ := fun s i => ∑ b : Fin 3, ∫ x,
    ‖ψ.gradient s (i,b) x‖^2
  let L : Spins n → ℝ := fun s => ∫ x, ‖ψ.value s x‖^2
  rw [nuclearEnergy_eq_sum]
  have hbound : (∑ s, ∑ i, ∑ j, S.charge j *
      (∫ x, coulombKernel (position x i - S.position j) * ‖ψ.value s x‖^2)) ≤
      ∑ s, ∑ i, ∑ j, S.charge j * (4 * η * K s i + 1 / (4 * η) * L s) := by
    apply Finset.sum_le_sum
    intro s _
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left
      (ψ.nuclear_coulomb_integrable_bound s i (S.position j) hη).2
      (le_trans (by norm_num) (S.charge_ge_one j))
  refine hbound.trans_eq ?_
  have hJ : ∀ s i, (∑ j, S.charge j * (4 * η * K s i + 1 / (4 * η) * L s)) =
      totalCharge S * (4 * η * K s i + 1 / (4 * η) * L s) := by
    intro s i
    rw [← Finset.sum_mul]
    rfl
  simp_rw [hJ]
  have hI : ∀ s, (∑ i, totalCharge S * (4 * η * K s i + 1 / (4 * η) * L s)) =
      (totalCharge S * (4 * η)) * (∑ i, K s i) +
      ((n : ℝ) * totalCharge S / (4 * η)) * L s := by
    intro s
    simp only [mul_add, Finset.sum_add_distrib, ← mul_assoc, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  simp_rw [hI]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hK : (∑ s, ∑ i, K s i) = 2 * kinetic ψ := by
    unfold K kinetic
    simp only [Fintype.sum_prod_type]
    ring
  rw [hK]
  change _ = 8 * η * totalCharge S * kinetic ψ +
    ((n : ℝ) * totalCharge S / (4 * η)) * (∑ s, L s)
  ring

end Coulomb
end
end

end OAI
end

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
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FiniteSubsequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open scoped Topology
noncomputable section
namespace Coulomb
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
variable {X:Type*} [TopologicalSpace X] [Nonempty X]

lemma finite_simultaneous_subsequence (u:ℕ → ι → X)
    (hc:∀ i (φ:ℕ → ℕ),StrictMono φ → ∃ v:X,∃ ψ:ℕ → ℕ,StrictMono ψ ∧
      Tendsto (fun n => u (φ (ψ n)) i) atTop (𝓝 v)) :
    ∃ v:ι → X,∃ φ:ℕ → ℕ,StrictMono φ ∧ ∀ i,Tendsto (fun n => u (φ n) i) atTop (𝓝 (v i)) := by
  have H (s:Finset ι) : ∃ v:ι → X,∃ φ:ℕ → ℕ,StrictMono φ ∧
      ∀ i∈s,Tendsto (fun n => u (φ n) i) atTop (𝓝 (v i)) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨fun _ => Classical.ofNonempty,id,strictMono_id,by simp⟩
    | @insert i s his ih =>
      obtain ⟨v,φ,hφ,hv⟩ := ih
      obtain ⟨w,ψ,hψ,hw⟩ := hc i φ hφ
      refine ⟨Function.update v i w,φ ∘ ψ,hφ.comp hψ,?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl|hj
      · simpa only [Function.update_self,Function.comp_def] using hw
      · have hji:j≠i := by intro he; subst j; contradiction
        simpa only [Function.update_of_ne hji,Function.comp_def] using
          (hv j hj).comp hψ.tendsto_atTop
  obtain ⟨v,φ,hφ,hv⟩ := H Finset.univ
  exact ⟨v,φ,hφ,fun i => hv i (Finset.mem_univ i)⟩
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_WeakSchwartzDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology SchwartzMap LineDeriv FourierTransform ComplexConjugate ContDiff
noncomputable section
namespace Coulomb
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private lemma compact_mul_memLp_integrable (f:E → ℂ) (hf:Continuous f)
    (hc:HasCompactSupport f) (u:E → ℂ) (hu:MemLp u 2 volume) :
    Integrable (fun x => f x*u x) :=
  (hf.memLp_of_hasCompactSupport hc (p:=2)).integrable_mul hu
private lemma compact_complex_integral_decompose (f:E → ℂ) (hf:Continuous f)
    (hc:HasCompactSupport f) (u:E → ℂ) (hu:MemLp u 2 volume) :
    (∫ x,f x*u x)=(∫ x,((f x).re:ℂ)*u x)+Complex.I*(∫ x,((f x).im:ℂ)*u x) := by
  have hr := compact_mul_memLp_integrable _
    (Complex.continuous_ofReal.comp (Complex.continuous_re.comp hf))
    (hc.comp_left (g:= fun z:ℂ => (z.re:ℂ)) (by simp)) u hu
  have hi := compact_mul_memLp_integrable _
    (Complex.continuous_ofReal.comp (Complex.continuous_im.comp hf))
    (hc.comp_left (g:= fun z:ℂ => (z.im:ℂ)) (by simp)) u hu
  have he (x:E) : f x*u x=((f x).re:ℂ)*u x+Complex.I*(((f x).im:ℂ)*u x) := by
    conv_lhs => rw [←(f x).re_add_im]
    ring
  simp_rw [he]
  change Integrable (fun x => ((f x).re:ℂ)*u x) at hr
  change Integrable (fun x => ((f x).im:ℂ)*u x) at hi
  rw [integral_add hr (hi.const_mul _),integral_const_mul]

lemma weak_directional_complex_test {u d : E → ℂ} (hu : MemLp u 2 volume)
    (hd : MemLp d 2 volume) (a : E)
    (hw : ∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,(fderiv ℝ φ x a:ℂ)*u x)=-(∫ x,(φ x:ℂ)*d x))
    (φ : E → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x,fderiv ℝ φ x a*u x)=-(∫ x,φ x*d x) := by
  have hr := hw (fun x => (φ x).re) (Complex.reCLM.contDiff.comp hφ) (hc.comp_left rfl)
  have hi := hw (fun x => (φ x).im) (Complex.imCLM.contDiff.comp hφ) (hc.comp_left rfl)
  have hdr (x:E) : fderiv ℝ (fun y => (φ y).re) x a=(fderiv ℝ φ x a).re := by
    exact congrArg (fun L:E →L[ℝ] ℝ => L a) ((Complex.reCLM.hasFDerivAt.comp x ((hφ.differentiable (by simp)) x).hasFDerivAt).fderiv)
  have hdi (x:E) : fderiv ℝ (fun y => (φ y).im) x a=(fderiv ℝ φ x a).im := by
    exact congrArg (fun L:E →L[ℝ] ℝ => L a) ((Complex.imCLM.hasFDerivAt.comp x ((hφ.differentiable (by simp)) x).hasFDerivAt).fderiv)
  have hD : Continuous (fun x => fderiv ℝ φ x a) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  rw [compact_complex_integral_decompose _ hD (hc.fderiv_apply ℝ a) u hu,
    compact_complex_integral_decompose _ hφ.continuous hc d hd]
  simp only [hdr] at hr
  simp only [hdi] at hi
  rw [hr,hi]
  ring

section
omit [MeasurableSpace E] [BorelSpace E]

private lemma weakCut_smooth (k:ℕ) : ContDiff ℝ ∞ (weakCut (E:=E) k) :=
  (weakCutBump (E:=E)).contDiff.comp (contDiff_const.smul contDiff_id)
private lemma weakCut_compact (k:ℕ) : HasCompactSupport (weakCut (E:=E) k) := by
  exact (weakCutBump (E:=E)).hasCompactSupport.comp_homeomorph
    (Homeomorph.smul (Units.mk0 (((k:ℝ)+1)⁻¹) (by positivity)))
private lemma weakCut_fderiv (k:ℕ) (x a:E) :
    fderiv ℝ (weakCut k) x a=((k:ℝ)+1)⁻¹*fderiv ℝ (weakCutBump (E:=E)) (((k:ℝ)+1)⁻¹ • x) a := by
  have h := (((weakCutBump (E:=E)).contDiff (n:=⊤)).differentiable (by simp) _).hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜:=ℝ) x).const_smul (((k:ℝ)+1)⁻¹))
  have HH := congrArg (fun L:E →L[ℝ] ℝ => L a) h.fderiv
  unfold weakCut
  simpa only [Function.comp_def,Pi.smul_apply,id_eq,ContinuousLinearMap.comp_apply,smul_apply,ContinuousLinearMap.id_apply,map_smul,smul_eq_mul] using HH
private lemma weakCut_bound : ∃ C:ℝ,0 ≤ C ∧ ∀ k x a,
    |fderiv ℝ (weakCut (E:=E) k) x a| ≤ ((k:ℝ)+1)⁻¹*C*‖a‖ := by
  obtain ⟨C,hC⟩ := (((weakCutBump (E:=E)).contDiff (n:=⊤)).continuous_fderiv (by simp)).bounded_above_of_compact_support
    ((weakCutBump (E:=E)).hasCompactSupport.fderiv ℝ)
  refine ⟨C,(norm_nonneg _).trans (hC 0),?_⟩
  intro k x a
  rw [weakCut_fderiv,abs_mul,abs_of_pos (by positivity : (0:ℝ)<((k:ℝ)+1)⁻¹)]
  calc
    _ ≤ ((k:ℝ)+1)⁻¹*(C*‖a‖) := mul_le_mul_of_nonneg_left
      (((fderiv ℝ (weakCutBump (E:=E)) _).le_opNorm a).trans (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))) (by positivity)
    _ = _ := by ring
private lemma weakCut_tendsto (x:E) : Tendsto (fun k => weakCut k x) atTop (𝓝 1) := by
  have ht : Tendsto (fun k:ℕ => ((k:ℝ)+1)⁻¹ • x) atTop (𝓝 (0:E)) := by
    have hi : Tendsto (fun k:ℕ => ((k:ℝ)+1)⁻¹) atTop (𝓝 (0:ℝ)) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa using hi.smul_const x
  have H := ((weakCutBump (E:=E)).continuous.tendsto (0:E)).comp ht
  have h1 : (weakCutBump (E:=E)) (0:E)=1 :=
    (weakCutBump (E:=E)).one_of_mem_closedBall (by simp [weakCutBump])
  simpa only [weakCut,Function.comp_def,h1] using H

end

lemma weak_directional_schwartz_test {u d : E → ℂ} (hu : MemLp u 2 volume)
    (hd : MemLp d 2 volume) (a : E)
    (hw : ∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,(fderiv ℝ φ x a:ℂ)*u x)=-(∫ x,(φ x:ℂ)*d x))
    (Φ : 𝓢(E,ℂ)) :
    (∫ x,(∂_{a} Φ) x*u x)=-(∫ x,Φ x*d x) := by
  obtain ⟨C,hC,hb⟩ := weakCut_bound (E:=E)
  have hinv (k:ℕ) : ((k:ℝ)+1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by have := Nat.cast_nonneg (α:=ℝ) k; linarith)
  have hi0 : Tendsto (fun k:ℕ => ((k:ℝ)+1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hdt (x:E) : Tendsto (fun k => fderiv ℝ (weakCut k) x a) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun k => hb k x a)
    simpa using (hi0.mul_const C).mul_const ‖a‖
  have hc0 (k:ℕ) (x:E) : 0 ≤ weakCut k x := (weakCutBump (E:=E)).nonneg
  have hc1 (k:ℕ) (x:E) : weakCut k x ≤ 1 := (weakCutBump (E:=E)).le_one
  let F : ℕ → E → ℂ := fun k x =>
    ((fderiv ℝ (weakCut k) x a:ℂ)*Φ x+(weakCut k x:ℂ)*(∂_{a} Φ) x)*u x
  let G : ℕ → E → ℂ := fun k x => (weakCut k x:ℂ)*Φ x*d x
  have he (k:ℕ) : (∫ x,F k x)=-(∫ x,G k x) := by
    let φ : E → ℂ := fun x => (weakCut k x:ℂ)*Φ x
    have hφ : ContDiff ℝ ∞ φ :=
      (Complex.ofRealCLM.contDiff.comp (weakCut_smooth k)).mul (Φ.smooth ⊤)
    have hf (x:E) : fderiv ℝ φ x a =
        (fderiv ℝ (weakCut k) x a:ℂ)*Φ x+(weakCut k x:ℂ)*(∂_{a} Φ) x := by
      have H := (((Complex.ofRealCLM.hasFDerivAt.comp x
        ((weakCut_smooth k).differentiable (by simp) x).hasFDerivAt)).mul (Φ.hasFDerivAt x)).fderiv
      have HH := congrArg (fun L:E →L[ℝ] ℂ => L a) H
      have HH2 : fderiv ℝ φ x a = (weakCut k x:ℂ)*fderiv ℝ Φ x a+Φ x*(fderiv ℝ (weakCut k) x a:ℂ) := by
        simpa only [φ,Pi.mul_def,Pi.mul_apply,Function.comp_def,add_apply,smul_apply,ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply,smul_eq_mul] using HH
      rw [SchwartzMap.lineDerivOp_apply_eq_fderiv,HH2]
      ring
    have H := weak_directional_complex_test hu hd a hw φ hφ
      (((weakCut_compact k).comp_left (by simp : ((0:ℝ):ℂ)=0)).mul_right)
    simpa only [hf,φ,F,G] using H
  have hφu : Integrable (fun x => ‖Φ x‖*‖u x‖) :=
    ((Φ.memLp 2 volume).norm).integrable_mul hu.norm
  have hdu : Integrable (fun x => ‖(∂_{a} Φ) x‖*‖u x‖) :=
    (((∂_{a} Φ).memLp 2 volume).norm).integrable_mul hu.norm
  have hφd : Integrable (fun x => ‖Φ x‖*‖d x‖) :=
    ((Φ.memLp 2 volume).norm).integrable_mul hd.norm
  have hFm (k:ℕ) : AEStronglyMeasurable (F k) volume := by
    exact (((Complex.continuous_ofReal.comp
      (((weakCut_smooth k).continuous_fderiv (by simp)).clm_apply (continuous_const (y:=a)))).mul Φ.continuous).add
      ((Complex.continuous_ofReal.comp (weakCut_smooth k).continuous).mul
        (∂_{a} Φ).continuous)).aestronglyMeasurable.mul hu.aestronglyMeasurable
  have hF : Tendsto (fun k => ∫ x,F k x) atTop (𝓝 (∫ x,(∂_{a} Φ) x*u x)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => C*‖a‖*(‖Φ x‖*‖u x‖)+‖(∂_{a} Φ) x‖*‖u x‖)
      hFm ((hφu.const_mul _).add hdu)
    · intro k
      filter_upwards [] with x
      dsimp [F]
      rw [norm_mul]
      have H1 : ‖(fderiv ℝ (weakCut k) x a:ℂ)‖ ≤ C*‖a‖ := by
        rw [Complex.norm_real,Real.norm_eq_abs]
        exact (hb k x a).trans (by nlinarith [mul_nonneg hC (norm_nonneg a),hinv k])
      have H2 : ‖(weakCut k x:ℂ)‖ ≤ 1 := by
        simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hc0 k x)] using hc1 k x
      calc
        _ ≤ (‖(fderiv ℝ (weakCut k) x a:ℂ)‖*‖Φ x‖+
          ‖(weakCut k x:ℂ)‖*‖(∂_{a} Φ) x‖)*‖u x‖ := by
          have HH := norm_add_le ((fderiv ℝ (weakCut k) x a:ℂ)*Φ x) ((weakCut k x:ℂ)*(∂_{a} Φ) x)
          simpa only [norm_mul] using mul_le_mul_of_nonneg_right HH (norm_nonneg (u x))
        _ ≤ (C*‖a‖*‖Φ x‖+1*‖(∂_{a} Φ) x‖)*‖u x‖ :=
          mul_le_mul_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_right H1 (norm_nonneg _))
            (mul_le_mul_of_nonneg_right H2 (norm_nonneg _))) (norm_nonneg _)
        _ = _ := by ring
    · filter_upwards [] with x
      have H := (((Complex.continuous_ofReal.tendsto 0).comp (hdt x)).mul_const (Φ x)).add
        (((Complex.continuous_ofReal.tendsto 1).comp (weakCut_tendsto x)).mul_const ((∂_{a} Φ) x))
      simpa only [F,Complex.ofReal_zero,zero_mul,Complex.ofReal_one,one_mul,zero_add,Function.comp_apply] using H.mul_const (u x)
  have hG : Tendsto (fun k => ∫ x,G k x) atTop (𝓝 (∫ x,Φ x*d x)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖Φ x‖*‖d x‖)
      (fun k => (((Complex.continuous_ofReal.comp (weakCut_smooth k).continuous).mul
        Φ.continuous).aestronglyMeasurable.mul hd.aestronglyMeasurable)) hφd
    · intro k
      filter_upwards [] with x
      dsimp [G]
      rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hc0 k x)]
      nlinarith [hc1 k x,norm_nonneg (Φ x),norm_nonneg (d x),mul_nonneg (norm_nonneg (Φ x)) (norm_nonneg (d x))]
    · filter_upwards [] with x
      simpa only [G,Complex.ofReal_one,one_mul,Function.comp_apply,Pi.mul_apply] using
        (((Complex.continuous_ofReal.tendsto 1).comp (weakCut_tendsto x)).mul_const (Φ x)).mul_const (d x)
  exact tendsto_nhds_unique hF (by simpa only [he] using hG.neg)

lemma l2_weakDeriv_tempered {u d : Lp ℂ 2 (volume:Measure E)} (a:E)
    (hw : ∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,(fderiv ℝ φ x a:ℂ)*u x)=-(∫ x,(φ x:ℂ)*d x)) :
    ∂_{a} (u:𝓢'(E,ℂ))=(d:𝓢'(E,ℂ)) := by
  ext Φ
  simp only [TemperedDistribution.lineDerivOp_apply_apply,map_neg,Lp.toTemperedDistribution_apply,smul_eq_mul]
  have H := weak_directional_schwartz_test (Lp.memLp u) (Lp.memLp d) a hw Φ
  simpa only [neg_neg] using congrArg Neg.neg H
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_WeakFourierDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology SchwartzMap LineDeriv FourierTransform ComplexConjugate ContDiff
noncomputable section
namespace Coulomb
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma l2_weakDeriv_fourier {u d : Lp ℂ 2 (volume:Measure E)} (a:E)
    (hw : ∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,(fderiv ℝ φ x a:ℂ)*u x)=-(∫ x,(φ x:ℂ)*d x)) :
    (𝓕 d : Lp ℂ 2 (volume:Measure E)) =ᵐ[volume]
      fun ξ => (2*Real.pi*Complex.I)*(inner ℝ ξ a:ℂ)*(𝓕 u : Lp ℂ 2 (volume:Measure E)) ξ := by
  have H := congrArg (fun T:𝓢'(E,ℂ) => 𝓕 T) (l2_weakDeriv_tempered a hw)
  rw [TemperedDistribution.fourier_lineDerivOp_eq,Lp.fourier_toTemperedDistribution_eq,
    Lp.fourier_toTemperedDistribution_eq] at H
  have hg : Continuous (fun ξ:E => (2*Real.pi*Complex.I)*(inner ℝ ξ a:ℂ)) := by fun_prop
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕 d : Lp ℂ 2 (volume:Measure E))).locallyIntegrable (by norm_num))
    (((Lp.memLp (𝓕 u : Lp ℂ 2 (volume:Measure E))).locallyIntegrable (by norm_num)).continuous_mul hg)
  intro φ hφ hc
  let χ : E → ℂ := fun x => (φ x:ℂ)
  have hχ : ContDiff ℝ ∞ χ := Complex.ofRealCLM.contDiff.comp hφ
  have hχc : HasCompactSupport χ := hc.comp_left (g:=fun r:ℝ => (r:ℂ)) (by simp)
  let Φ : 𝓢(E,ℂ) := hχc.toSchwartzMap hχ
  have ht : (fun ξ:E => (inner ℝ ξ a:ℂ)).HasTemperateGrowth := by fun_prop
  have HH := congrArg (fun T:𝓢'(E,ℂ) => T Φ) H
  simp only [smul_apply,smul_eq_mul,
    TemperedDistribution.smulLeftCLM_apply_apply,Lp.toTemperedDistribution_apply] at HH
  change (2*Real.pi*Complex.I)*(∫ x,
    (SchwartzMap.smulLeftCLM ℂ (fun ξ:E => (inner ℝ ξ a:ℂ)) Φ) x * (𝓕 u : Lp ℂ 2 (volume:Measure E)) x)=
      ∫ x,Φ x*(𝓕 d : Lp ℂ 2 (volume:Measure E)) x at HH
  rw [←integral_const_mul] at HH
  calc
    _=∫ x,Φ x*(𝓕 d : Lp ℂ 2 (volume:Measure E)) x := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [Φ,χ,HasCompactSupport.toSchwartzMap_toFun,Complex.real_smul]
    _= _ := HH.symm
    _= _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [SchwartzMap.smulLeftCLM_apply ht,smul_eq_mul,Φ,χ,
        HasCompactSupport.toSchwartzMap_toFun,Complex.real_smul]
      ring

lemma l2_weakDeriv_fourier_energy {u d : Lp ℂ 2 (volume:Measure E)} (a:E)
    (hw : ∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,(fderiv ℝ φ x a:ℂ)*u x)=-(∫ x,(φ x:ℂ)*d x)) :
    Integrable (fun ξ => (2*Real.pi*inner ℝ ξ a)^2*
      ‖(𝓕 u : Lp ℂ 2 (volume:Measure E)) ξ‖^2) ∧
    (∫ ξ,(2*Real.pi*inner ℝ ξ a)^2*‖(𝓕 u : Lp ℂ 2 (volume:Measure E)) ξ‖^2)=‖d‖^2 := by
  have h := l2_weakDeriv_fourier a hw
  have he : (fun ξ => ‖(𝓕 d : Lp ℂ 2 (volume:Measure E)) ξ‖^2) =ᵐ[volume]
      fun ξ => (2*Real.pi*inner ℝ ξ a)^2*‖(𝓕 u : Lp ℂ 2 (volume:Measure E)) ξ‖^2 := by
    filter_upwards [h] with ξ hξ
    rw [hξ,fourierMultiplier_norm_sq]
  refine ⟨((Lp.memLp (𝓕 d : Lp ℂ 2 (volume:Measure E))).integrable_norm_pow (by norm_num)).congr he,?_⟩
  rw [←integral_congr_ae he,←l2_norm_sq_fourier]
  exact congrArg (fun t:ℝ => t^2) ((Lp.fourierTransformₗᵢ E ℂ).norm_map d)
end Coulomb
end

end
section
open MeasureTheory Set Filter
open scoped ENNReal Topology ComplexConjugate
noncomputable section
namespace Coulomb
variable {X:Type*} [MeasurableSpace X] {μ:Measure X}
lemma cutL2_ae (s:Set X) (hs:MeasurableSet s) (u:Lp ℂ 2 μ) :
    cutL2 s hs u =ᵐ[μ] s.indicator u := MemLp.coeFn_toLp _
lemma cutL2_norm_le (s:Set X) (hs:MeasurableSet s) (u:Lp ℂ 2 μ) :
    ‖cutL2 s hs u‖≤‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [cutL2_ae s hs u] with x hx
  rw [hx]
  by_cases hx:x∈s <;> simp [hx]
lemma cutL2_sub (s:Set X) (hs:MeasurableSet s) (u v:Lp ℂ 2 μ) :
    cutL2 s hs (u-v)=cutL2 s hs u-cutL2 s hs v := by
  apply Lp.ext
  filter_upwards [cutL2_ae s hs (u-v),cutL2_ae s hs u,cutL2_ae s hs v,
    Lp.coeFn_sub u v,Lp.coeFn_sub (cutL2 s hs u) (cutL2 s hs v)] with x h h1 h2 huv h3
  rw [h,h3]
  simp only [Pi.sub_apply]
  rw [h1,h2]
  by_cases hx:x∈s
  · simp only [Set.indicator_of_mem hx,huv,Pi.sub_apply]
  · simp only [Set.indicator_of_notMem hx,sub_self]
lemma cutL2_add_compl (s:Set X) (hs:MeasurableSet s) (u:Lp ℂ 2 μ) :
    cutL2 s hs u+cutL2 sᶜ hs.compl u=u := by
  apply Lp.ext
  filter_upwards [cutL2_ae s hs u,cutL2_ae sᶜ hs.compl u,
    Lp.coeFn_add (cutL2 s hs u) (cutL2 sᶜ hs.compl u)] with x h1 h2 h3
  rw [h3]
  simp only [Pi.add_apply]
  rw [h1,h2]
  by_cases hx:x∈s <;> simp [hx]
lemma l2_norm_sq_integral (u:Lp ℂ 2 μ) : ‖u‖^2=∫ x,‖u x‖^2 ∂μ := by
  have h := congrArg Complex.re (L2.inner_def u u (𝕜:=ℂ))
  rw [inner_self_eq_norm_sq_to_K] at h
  change ((‖u‖:ℂ)^2).re=(∫ x,inner ℂ (u x) (u x) ∂μ).re at h
  rw [←Complex.ofReal_pow,Complex.ofReal_re] at h
  rw [h]
  change RCLike.re (∫ x,inner ℂ (u x) (u x) ∂μ)=_
  rw [←integral_re (L2.integrable_inner (𝕜:=ℂ) u u)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [inner_self_eq_norm_sq_to_K,←Complex.ofReal_pow]
lemma cutL2_norm_sq (s:Set X) (hs:MeasurableSet s) (u:Lp ℂ 2 μ) :
    ‖cutL2 s hs u‖^2=∫ x in s,‖u x‖^2 ∂μ := by
  rw [l2_norm_sq_integral,←integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [cutL2_ae s hs u] with x hx
  rw [hx]
  by_cases h:x∈s <;> simp [h]
end Coulomb
end

end
section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology FourierTransform BigOperators ContDiff
noncomputable section
namespace Coulomb
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
lemma l2_gradient_fourier_moment
    (u:Lp ℂ 2 (volume:Measure (EuclideanSpace ℝ ι)))
    (d:ι → Lp ℂ 2 (volume:Measure (EuclideanSpace ℝ ι)))
    (hw:∀ i (φ:EuclideanSpace ℝ ι → ℝ),ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,(fderiv ℝ φ x (EuclideanSpace.single i 1):ℂ)*u x)=-(∫ x,(φ x:ℂ)*d i x)) :
    Integrable (fun ξ => (2*Real.pi)^2*‖ξ‖^2*‖(𝓕 u:Lp ℂ 2 volume) ξ‖^2) ∧
    (∫ ξ,(2*Real.pi)^2*‖ξ‖^2*‖(𝓕 u:Lp ℂ 2 volume) ξ‖^2)=∑ i,‖d i‖^2 := by
  have H i := l2_weakDeriv_fourier_energy (EuclideanSpace.single i 1) (hw i)
  have he (ξ:EuclideanSpace ℝ ι) :
      (∑ i,(2*Real.pi*inner ℝ ξ (EuclideanSpace.single i 1))^2*‖(𝓕 u:Lp ℂ 2 volume) ξ‖^2)=
        (2*Real.pi)^2*‖ξ‖^2*‖(𝓕 u:Lp ℂ 2 volume) ξ‖^2 := by
    simp only [EuclideanSpace.inner_single_right,conj_trivial,one_mul,mul_pow]
    rw [←Finset.sum_mul,←Finset.mul_sum,←EuclideanSpace.real_norm_sq_eq]
  have hi := integrable_finsetSum Finset.univ (fun i _ => (H i).1)
  refine ⟨hi.congr (Filter.Eventually.of_forall he),?_⟩
  rw [←integral_congr_ae (Filter.Eventually.of_forall he),integral_finsetSum _ (fun i _ => (H i).1)]
  exact Finset.sum_congr rfl (fun i _ => (H i).2)

lemma l2_fourier_tail_bound
    (u:Lp ℂ 2 (volume:Measure (EuclideanSpace ℝ ι)))
    (d:ι → Lp ℂ 2 (volume:Measure (EuclideanSpace ℝ ι)))
    (hw:∀ i (φ:EuclideanSpace ℝ ι → ℝ),ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,(fderiv ℝ φ x (EuclideanSpace.single i 1):ℂ)*u x)=-(∫ x,(φ x:ℂ)*d i x))
    {R:ℝ} (hR:0<R) :
    (2*Real.pi)^2*R^2*‖cutL2 (Metric.ball (0:EuclideanSpace ℝ ι) R)ᶜ
      measurableSet_ball.compl (𝓕 u)‖^2 ≤ ∑ i,‖d i‖^2 := by
  obtain ⟨hi,he⟩ := l2_gradient_fourier_moment u d hw
  rw [cutL2_norm_sq,←he,←integral_const_mul]
  apply (integral_mono_ae
    (((Lp.memLp (𝓕 u:Lp ℂ 2 volume)).integrable_norm_pow (by norm_num)).restrict.const_mul _)
    hi.restrict ?_).trans
  · exact setIntegral_le_integral hi (Filter.Eventually.of_forall fun ξ => by positivity)
  · filter_upwards [ae_restrict_mem measurableSet_ball.compl] with ξ hξ
    have hξR : R≤‖ξ‖ := by simpa [Metric.mem_ball,dist_zero_right,not_lt] using hξ
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le hξR 2) (sq_nonneg _)) (sq_nonneg _)

lemma bounded_gradient_frequency_tight
    (u:ℕ → Lp ℂ 2 (volume:Measure (EuclideanSpace ℝ ι)))
    (d:ℕ → ι → Lp ℂ 2 (volume:Measure (EuclideanSpace ℝ ι)))
    (hw:∀ n i (φ:EuclideanSpace ℝ ι → ℝ),ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,(fderiv ℝ φ x (EuclideanSpace.single i 1):ℂ)*u n x)=-(∫ x,(φ x:ℂ)*d n i x))
    (K:ℝ) (hK:∀ n,∑ i,‖d n i‖^2≤K) (ε:ℝ) (hε:0<ε) :
    ∃ R:ℝ,0<R ∧ ∀ n,‖cutL2 (Metric.ball (0:EuclideanSpace ℝ ι) R)ᶜ
      measurableSet_ball.compl (𝓕 (u n))‖≤ε := by
  have hKn:0≤K := (Finset.sum_nonneg fun i _ => sq_nonneg ‖d 0 i‖).trans (hK 0)
  let R:ℝ := (Real.sqrt K+1)/(2*Real.pi*ε)
  have hR:0<R := by dsimp [R]; positivity
  refine ⟨R,hR,?_⟩
  intro n
  have h := (l2_fourier_tail_bound (u n) (d n) (hw n) hR).trans (hK n)
  have he : (2*Real.pi)^2*R^2*ε^2=(Real.sqrt K+1)^2 := by
    dsimp [R]
    field_simp
  have hlt:K<(Real.sqrt K+1)^2 := by
    have hh:=Real.sq_sqrt hKn
    have hp:=Real.sqrt_nonneg K
    nlinarith
  have hc : 0<(2*Real.pi)^2*R^2 := by positivity
  by_contra hn
  have hp : ε<‖cutL2 (Metric.ball (0:EuclideanSpace ℝ ι) R)ᶜ measurableSet_ball.compl (𝓕 (u n))‖ := lt_of_not_ge hn
  have hs := sq_lt_sq₀ hε.le (norm_nonneg _) |>.mpr hp
  nlinarith
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_H1VectorL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexConjugate ContDiff BigOperators
noncomputable section
namespace Coulomb
namespace H1Vector
variable {n:ℕ}
lemma gradientL2_ae (u:H1Vector n) (s:Spins n) (a:Fin n × Fin 3) :
    (u.gradientL2 s a:Configuration n → ℂ)=ᵐ[volume]u.gradient s a :=
  (u.partial_L2 s a).coeFn_toLp
lemma mass_eq_norm (u:H1Vector n) : mass u=∑ s,‖u.valueL2 s‖^2 := by
  apply Finset.sum_congr rfl
  intro s _
  rw [l2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [u.valueL2_ae s] with x hx
  rw [hx]
lemma kinetic_eq_norm (u:H1Vector n) : kinetic u=(1/2:ℝ)*∑ s,∑ a,‖u.gradientL2 s a‖^2 := by
  unfold kinetic
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro a _
  rw [l2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [u.gradientL2_ae s a] with x hx
  rw [hx]
lemma weak_partial_L2 (u:H1Vector n) (s:Spins n) (a:Fin n × Fin 3)
    (φ:Configuration n → ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) :
    (∫ x,(fderiv ℝ φ x (EuclideanSpace.single a 1):ℂ)*u.valueL2 s x)=
      -(∫ x,(φ x:ℂ)*u.gradientL2 s a x) := by
  have h1:(∫ x,(fderiv ℝ φ x (EuclideanSpace.single a 1):ℂ)*u.valueL2 s x)=
      ∫ x,u.value s x*(fderiv ℝ φ x (EuclideanSpace.single a 1):ℂ) := by
    apply integral_congr_ae
    filter_upwards [u.valueL2_ae s] with x hx
    rw [hx,mul_comm]
  have h2:(∫ x,(φ x:ℂ)*u.gradientL2 s a x)=∫ x,u.gradient s a x*(φ x:ℂ) := by
    apply integral_congr_ae
    filter_upwards [u.gradientL2_ae s a] with x hx
    rw [hx,mul_comm]
  rw [h1,h2]
  exact u.weak_partial s a φ hφ hc

lemma ofL2_valueL2 (v:Spins n → Lp ℂ 2 (volume:Measure (Configuration n)))
    (g:Spins n → (Fin n × Fin 3) → Lp ℂ 2 (volume:Measure (Configuration n))) hw (s:Spins n) :
    (ofL2 v g hw).valueL2 s=v s := by
  apply Lp.ext
  exact (Lp.memLp (v s)).coeFn_toLp
lemma ofL2_gradientL2 (v:Spins n → Lp ℂ 2 (volume:Measure (Configuration n)))
    (g:Spins n → (Fin n × Fin 3) → Lp ℂ 2 (volume:Measure (Configuration n))) hw (s:Spins n) (a:Fin n × Fin 3) :
    (ofL2 v g hw).gradientL2 s a=g s a := by
  apply Lp.ext
  exact (Lp.memLp (g s a)).coeFn_toLp
end H1Vector

lemma antisymmetric_iff_valueL2 {n:ℕ} (u:H1Vector n) : Antisymmetric u ↔
    ∀ (p:Equiv.Perm (Fin n)) (s:Spins n),
      Lp.compMeasurePreservingₗᵢ ℂ (permute p) (permute_measurePreserving p) (u.valueL2 (s ∘ p))=
        ((p.sign:ℤ):ℂ) • u.valueL2 s := by
  constructor
  · intro ha p s
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (u.valueL2 (s ∘ p)) (permute_measurePreserving p),
      (permute_measurePreserving p).quasiMeasurePreserving.ae (u.valueL2_ae (s ∘ p)),
      Lp.coeFn_smul ((p.sign:ℤ):ℂ) (u.valueL2 s),u.valueL2_ae s,ha p s] with x h1 h2 h3 h4 h5
    change Lp.compMeasurePreserving (permute p) (permute_measurePreserving p) (u.valueL2 (s ∘ p)) x = _
    rw [h1,h3]
    change u.valueL2 (s ∘ p) (permute p x) = ((p.sign:ℤ):ℂ) * u.valueL2 s x
    rw [h2,h4]
    exact h5
  · intro ha p s
    have he:=Lp.ext_iff.mp (ha p s)
    filter_upwards [he,Lp.coeFn_compMeasurePreserving (u.valueL2 (s ∘ p)) (permute_measurePreserving p),
      (permute_measurePreserving p).quasiMeasurePreserving.ae (u.valueL2_ae (s ∘ p)),
      Lp.coeFn_smul ((p.sign:ℤ):ℂ) (u.valueL2 s),u.valueL2_ae s] with x he h1 h2 h3 h4
    change Lp.compMeasurePreserving (permute p) (permute_measurePreserving p) (u.valueL2 (s ∘ p)) x = _ at he
    rw [h1,h3] at he
    change u.valueL2 (s ∘ p) (permute p x) = ((p.sign:ℤ):ℂ) * u.valueL2 s x at he
    rwa [h2,h4] at he

lemma antisymmetric_strong_limit {n:ℕ} (u:ℕ → H1Vector n) (v:H1Vector n)
    (ha:∀ k,Antisymmetric (u k))
    (hv:∀ s,Tendsto (fun k => (u k).valueL2 s) atTop (𝓝 (v.valueL2 s))) : Antisymmetric v := by
  rw [antisymmetric_iff_valueL2]
  intro p s
  have h1:=((Lp.compMeasurePreservingₗᵢ ℂ (permute p) (permute_measurePreserving p)).continuous.tendsto
    (v.valueL2 (s ∘ p))).comp (hv (s ∘ p))
  have h2:=(hv s).const_smul (((p.sign:ℤ):ℂ))
  exact tendsto_nhds_unique h1 (by
    convert h2 using 1
    all_goals try with_reducible_and_instances rfl
    apply funext
    intro k
    exact (antisymmetric_iff_valueL2 (u k)).mp (ha k) p s)
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_L1L2Fourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology SchwartzMap FourierTransform ComplexConjugate ContDiff
noncomputable section
namespace Coulomb
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
lemma l1_l2_fourier_ae (u:Lp ℂ 2 (volume:Measure E)) (hu:Integrable (u:E → ℂ)) :
    (𝓕 u : Lp ℂ 2 (volume:Measure E)) =ᵐ[volume] 𝓕 (u:E → ℂ) := by
  have hf : Continuous (𝓕 (u:E → ℂ)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hu
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕 u : Lp ℂ 2 (volume:Measure E))).locallyIntegrable (by norm_num))
    hf.locallyIntegrable
  intro φ hφ hc
  let χ:E → ℂ := fun x => (φ x:ℂ)
  have hχ:ContDiff ℝ ∞ χ := Complex.ofRealCLM.contDiff.comp hφ
  have hcχ:HasCompactSupport χ := hc.comp_left (g:=fun r:ℝ => (r:ℂ)) (by simp)
  let Φ:𝓢(E,ℂ) := hcχ.toSchwartzMap hχ
  have h := congrArg (fun T:𝓢'(E,ℂ) => T Φ) (Lp.fourier_toTemperedDistribution_eq u)
  simp only [TemperedDistribution.fourier_apply,Lp.toTemperedDistribution_apply,smul_eq_mul] at h
  have hi := VectorFourier.integral_fourierIntegral_smul_eq_flip (L:=innerₗ E) (μ:=volume) (ν:=volume)
    Real.continuous_fourierChar continuous_inner Φ.integrable hu
  calc
    _ = ∫ x,Φ x * (𝓕 u : Lp ℂ 2 (volume:Measure E)) x := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [Φ,χ,HasCompactSupport.toSchwartzMap_toFun,Complex.real_smul]
    _ = ∫ x,(𝓕 Φ) x * u x := h.symm
    _ = ∫ x,Φ x * 𝓕 (u:E → ℂ) x := by
      rw [SchwartzMap.fourier_coe]
      simpa using! hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [Φ,χ,HasCompactSupport.toSchwartzMap_toFun,Complex.real_smul]
end Coulomb
end

end
section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology FourierTransform ComplexConjugate
noncomputable section
namespace Coulomb
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
lemma cutL2_integrable (s:Set E) (hs:MeasurableSet s) (hμ:volume s≠∞)
    (u:Lp ℂ 2 (volume:Measure E)) : Integrable (cutL2 s hs u : E → ℂ) := by
  have h := L2.integrable_inner (𝕜:=ℂ) (indicatorConstLp 2 hs hμ (1:ℂ)) u
  apply h.congr
  filter_upwards [indicatorConstLp_coeFn (p:=2) (hs:=hs) (hμs:=hμ) (c:=(1:ℂ)),cutL2_ae s hs u] with x h1 h2
  rw [h1,h2]
  by_cases hx:x∈s <;> simp [hx]

lemma fourierPlaneL2_ae (s:Set E) (hs:MeasurableSet s) (hμ:volume s≠∞) (ξ:E) :
    fourierPlaneL2 s hs hμ ξ =ᵐ[volume] fourierPlane s ξ := MemLp.coeFn_toLp _
lemma fourierPlaneL2_norm (s:Set E) (hs:MeasurableSet s) (hμ:volume s≠∞) (ξ:E) :
    ‖fourierPlaneL2 s hs hμ ξ‖ ≤ ‖indicatorConstLp 2 hs hμ (1:ℂ)‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [fourierPlaneL2_ae s hs hμ ξ,
    indicatorConstLp_coeFn (p:=2) (hs:=hs) (hμs:=hμ) (c:=(1:ℂ))] with x h1 h2
  rw [h1,h2]
  by_cases hx:x∈s <;> simp [fourierPlane,hx,Circle.norm_coe]
lemma fourier_cut_inner (s:Set E) (hs:MeasurableSet s) (hμ:volume s≠∞)
    (u:Lp ℂ 2 (volume:Measure E)) (ξ:E) :
    𝓕 (cutL2 s hs u:E → ℂ) ξ=inner ℂ (fourierPlaneL2 s hs hμ ξ) u := by
  rw [Real.fourier_eq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fourierPlaneL2_ae s hs hμ ξ,cutL2_ae s hs u] with x h1 h2
  rw [h1,h2]
  by_cases hx:x∈s <;> simp [fourierPlane,hx,Circle.smul_def,mul_comm]
lemma fourier_cut_weak_tendsto (s:Set E) (hs:MeasurableSet s) (hμ:volume s≠∞)
    (u:ℕ → Lp ℂ 2 (volume:Measure E)) (v:Lp ℂ 2 (volume:Measure E))
    (hw:∀ w,Tendsto (fun n => inner ℂ w (u n)) atTop (𝓝 (inner ℂ w v))) (ξ:E) :
    Tendsto (fun n => 𝓕 (cutL2 s hs (u n):E → ℂ) ξ) atTop
      (𝓝 (𝓕 (cutL2 s hs v:E → ℂ) ξ)) := by
  simp_rw [fourier_cut_inner s hs hμ]
  exact hw _
end Coulomb
end

end
section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology FourierTransform ComplexConjugate
noncomputable section
namespace Coulomb
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
lemma fourier_cut_norm_bound (s:Set E) (hs:MeasurableSet s) (hμ:volume s≠∞)
    (u:Lp ℂ 2 (volume:Measure E)) (ξ:E) :
    ‖𝓕 (cutL2 s hs u:E → ℂ) ξ‖ ≤ ‖indicatorConstLp 2 hs hμ (1:ℂ)‖*‖u‖ := by
  rw [fourier_cut_inner s hs hμ]
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (fourierPlaneL2_norm s hs hμ ξ) (norm_nonneg u))

lemma fourier_double_cut_tendsto (s t:Set E) (hs:MeasurableSet s) (ht:MeasurableSet t)
    (hμ:volume s≠∞) (hν:volume t≠∞)
    (u:ℕ → Lp ℂ 2 (volume:Measure E)) (v:Lp ℂ 2 (volume:Measure E))
    (C:ℝ) (hb:∀ n,‖u n‖≤C)
    (hw:∀ w,Tendsto (fun n => inner ℂ w (u n)) atTop (𝓝 (inner ℂ w v))) :
    Tendsto (fun n => cutL2 t ht (𝓕 (cutL2 s hs (u n)))) atTop
      (𝓝 (cutL2 t ht (𝓕 (cutL2 s hs v)))) := by
  let A:ℝ := ‖indicatorConstLp 2 hs hμ (1:ℂ)‖
  let B:ℝ := A*(C+‖v‖)
  have hC:0≤C := (norm_nonneg (u 0)).trans (hb 0)
  have hA:0≤A := norm_nonneg _
  have hB:0≤B := mul_nonneg hA (add_nonneg hC (norm_nonneg v))
  let f:ℕ → E → ℂ := fun n ξ => 𝓕 (cutL2 s hs (u n):E → ℂ) ξ - 𝓕 (cutL2 s hs v:E → ℂ) ξ
  have hf (n:ℕ) : Continuous (f n) :=
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (cutL2_integrable s hs hμ (u n))).sub
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (cutL2_integrable s hs hμ v))
  have hfb (n:ℕ) (ξ:E) : ‖f n ξ‖≤B := by
    calc
      _≤‖𝓕 (cutL2 s hs (u n):E → ℂ) ξ‖+‖𝓕 (cutL2 s hs v:E → ℂ) ξ‖ := norm_sub_le _ _
      _≤A*‖u n‖+A*‖v‖ := add_le_add (fourier_cut_norm_bound s hs hμ _ _) (fourier_cut_norm_bound s hs hμ _ _)
      _≤A*C+A*‖v‖ := add_le_add (mul_le_mul_of_nonneg_left (hb n) hA) (le_refl _)
      _=B := by dsimp [B]; ring
  let : IsFiniteMeasure (volume.restrict t : Measure E) := ⟨by simpa using hν.lt_top⟩
  have hlim : Tendsto (fun n => ∫ ξ in t,‖f n ξ‖^2) atTop (𝓝 (0:ℝ)) := by
    have H := tendsto_integral_of_dominated_convergence (μ:=volume.restrict t)
      (F:=fun n ξ => ‖f n ξ‖^2) (f:=fun _ => (0:ℝ)) (fun _ => B^2)
      (fun n => ((hf n).norm.pow 2).aestronglyMeasurable) (integrable_const _)
      (fun n => Filter.Eventually.of_forall (fun ξ => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hfb n ξ) _))
      (Filter.Eventually.of_forall (fun ξ => by
        have h := (fourier_cut_weak_tendsto s hs hμ u v hw ξ).sub_const
          (𝓕 (cutL2 s hs v:E → ℂ) ξ)
        simpa [f] using h.norm.pow 2))
    simpa using H
  have he (n:ℕ) :
      ‖cutL2 t ht (𝓕 (cutL2 s hs (u n)))-cutL2 t ht (𝓕 (cutL2 s hs v))‖^2
        =∫ ξ in t,‖f n ξ‖^2 := by
    rw [←cutL2_sub,cutL2_norm_sq]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub (𝓕 (cutL2 s hs (u n))) (𝓕 (cutL2 s hs v))),
      ae_restrict_of_ae (l1_l2_fourier_ae _ (cutL2_integrable s hs hμ (u n))),
      ae_restrict_of_ae (l1_l2_fourier_ae _ (cutL2_integrable s hs hμ v))] with ξ h1 h2 h3
    simp only [h1,Pi.sub_apply,h2,h3,f]
  have hl := hlim.congr' (Filter.Eventually.of_forall fun n => (he n).symm)
  have hn := (Real.continuous_sqrt.tendsto (0:ℝ)).comp hl
  simp only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),Real.sqrt_zero] at hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_WeakHilbertCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open scoped Topology ComplexConjugate
noncomputable section
namespace Coulomb
variable {H:Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
 [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

lemma bounded_hilbert_weak_subsequence (u:ℕ → H) (C:ℝ) (hb:∀ n,‖u n‖≤C) :
    ∃ v:H, ‖v‖≤C ∧ ∃ φ:ℕ → ℕ,StrictMono φ ∧
      ∀ w:H,Tendsto (fun n => inner ℂ w (u (φ n))) atTop (𝓝 (inner ℂ w v)) := by
  let F : ℕ → WeakDual ℂ H := fun n => StrongDual.toWeakDual (InnerProductSpace.toDual ℂ H (u n))
  have hm (n:ℕ) : F n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0:StrongDual ℂ H) C := by
    change dist (WeakDual.toStrongDual (StrongDual.toWeakDual (InnerProductSpace.toDual ℂ H (u n)))) 0 ≤ C
    have hh (g:StrongDual ℂ H) : WeakDual.toStrongDual (StrongDual.toWeakDual g)=g := by
      ext x
      rfl
    rw [hh,dist_eq_norm]
    change ‖InnerProductSpace.toDual ℂ H (u n)-0‖≤ C
    simpa only [sub_zero,LinearIsometryEquiv.norm_map] using hb n
  obtain ⟨f,hf,φ,hφ,ht⟩ := (WeakDual.isSeqCompact_closedBall (𝕜:=ℂ) (E:=H) 0 C) hm
  let v:H := (InnerProductSpace.toDual ℂ H).symm (WeakDual.toStrongDual f)
  refine ⟨v,?_,φ,hφ,?_⟩
  · simpa only [Set.mem_preimage,Metric.mem_closedBall,dist_zero_right,
      ←(InnerProductSpace.toDual ℂ H).symm.norm_map] using hf
  · intro w
    have h := (WeakBilin.eval_continuous _ w).tendsto f |>.comp ht
    have he : WeakDual.toStrongDual f w=inner ℂ v w := by
      rw [←InnerProductSpace.toDual_apply_apply]
      exact congrArg (fun g:StrongDual ℂ H => g w)
        ((InnerProductSpace.toDual ℂ H).apply_symm_apply _).symm
    change Tendsto (fun n => inner ℂ (u (φ n)) w) atTop (𝓝 (WeakDual.toStrongDual f w)) at h
    rw [he] at h
    simpa only [Function.comp_def,inner_conj_symm] using (Complex.continuous_conj.tendsto _).comp h
end Coulomb
end

end
section
open Filter Set
open scoped Topology ComplexConjugate BigOperators
noncomputable section
namespace Coulomb
variable {H:Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
 [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
lemma bounded_finite_hilbert_weak_subsequence (u:ℕ → ι → H) (K:ℝ)
    (hb:∀ n,∑ i,‖u n i‖^2≤K) :
    ∃ v:ι → H,(∑ i,‖v i‖^2)≤K ∧ ∃ φ:ℕ → ℕ,StrictMono φ ∧
      ∀ i w,Tendsto (fun n => inner ℂ w (u (φ n) i)) atTop (𝓝 (inner ℂ w (v i))) := by
  let U:ℕ → PiLp 2 (fun _:ι => H) := fun n => WithLp.toLp 2 (u n)
  have hK:0≤K := (Finset.sum_nonneg fun i _ => sq_nonneg ‖u 0 i‖).trans (hb 0)
  have hU (n:ℕ) : ‖U n‖≤Real.sqrt K := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hK,PiLp.norm_sq_eq_of_L2]
    exact hb n
  obtain ⟨v,hv,φ,hφ,hw⟩ := bounded_hilbert_weak_subsequence U (Real.sqrt K) hU
  refine ⟨fun i => v i,?_,φ,hφ,?_⟩
  · rw [←PiLp.norm_sq_eq_of_L2 (fun _:ι => H) v]
    exact (pow_le_pow_left₀ (norm_nonneg _) hv 2).trans_eq (Real.sq_sqrt hK)
  · intro i w
    have h := hw (PiLp.single 2 i w)
    have he (z:PiLp 2 (fun _:ι => H)) : inner ℂ (PiLp.single 2 i w) z = inner ℂ w (z i) := by
      simp only [PiLp.inner_apply,PiLp.single_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji; simp [hji]
      · simp
    simpa only [he,U,WithLp.toLp_ofLp] using h

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
lemma weak_tendsto_norm_le {u:ℕ → H} {v:H} {C:ℝ} (hC:0≤C)
    (hw:∀ w,Tendsto (fun n => inner ℂ w (u n)) atTop (𝓝 (inner ℂ w v)))
    (hb:∀ᶠ n in atTop,‖u n‖≤C) : ‖v‖≤C := by
  have h := (hw v).norm
  have hh : ∀ᶠ n in atTop,‖inner ℂ v (u n)‖≤‖v‖*C := by
    filter_upwards [hb] with n hn
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hn (norm_nonneg _))
  have H := le_of_tendsto h hh
  rw [← inner_self_re_eq_norm, ← norm_sq_eq_re_inner] at H
  by_cases hv:‖v‖=0
  · rwa [hv]
  · have hp:0<‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    nlinarith
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_L2TightCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology FourierTransform ComplexConjugate
noncomputable section
namespace Coulomb
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
lemma cutL2_sub_self (s:Set E) (hs:MeasurableSet s) (u:Lp ℂ 2 (volume:Measure E)) :
    u-cutL2 s hs u=cutL2 sᶜ hs.compl u := by
  have h := cutL2_add_compl s hs u
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using h.symm)
lemma double_cut_approximation (s t:Set E) (hs:MeasurableSet s) (ht:MeasurableSet t)
    (u:Lp ℂ 2 (volume:Measure E)) :
    ‖(𝓕 u : Lp ℂ 2 (volume:Measure E))-cutL2 t ht (𝓕 (cutL2 s hs u))‖ ≤
      ‖cutL2 tᶜ ht.compl (𝓕 u)‖+‖cutL2 sᶜ hs.compl u‖ := by
  calc
    _≤‖(𝓕 u : Lp ℂ 2 (volume:Measure E))-cutL2 t ht (𝓕 u)‖+
        ‖cutL2 t ht (𝓕 u)-cutL2 t ht (𝓕 (cutL2 s hs u))‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _≤‖cutL2 tᶜ ht.compl (𝓕 u)‖+‖(𝓕 u : Lp ℂ 2 (volume:Measure E))-𝓕 (cutL2 s hs u)‖ := by
      rw [cutL2_sub_self,←cutL2_sub]
      exact add_le_add (le_refl _) (cutL2_norm_le t ht _)
    _= _ := by
      have h : ‖(𝓕 u : Lp ℂ 2 (volume:Measure E))-𝓕 (cutL2 s hs u)‖=‖u-cutL2 s hs u‖ := by
        change ‖(Lp.fourierTransformₗᵢ E ℂ) u-(Lp.fourierTransformₗᵢ E ℂ) (cutL2 s hs u)‖=_
        rw [←map_sub,(Lp.fourierTransformₗᵢ E ℂ).norm_map]
      rw [h,cutL2_sub_self]

lemma l2_tight_frequency_subsequence
    (u:ℕ → Lp ℂ 2 (volume:Measure E)) (C:ℝ) (hb:∀ n,‖u n‖≤C)
    (hspace:∀ ε:ℝ,0<ε → ∃ s:Set E,∃ hs:MeasurableSet s,volume s≠∞ ∧
      ∀ᶠ n in atTop,‖cutL2 sᶜ hs.compl (u n)‖≤ε)
    (hfreq:∀ ε:ℝ,0<ε → ∃ t:Set E,∃ ht:MeasurableSet t,volume t≠∞ ∧
      ∀ᶠ n in atTop,‖cutL2 tᶜ ht.compl (𝓕 (u n))‖≤ε) :
    ∃ v:Lp ℂ 2 (volume:Measure E),∃ φ:ℕ → ℕ,StrictMono φ ∧
      Tendsto (u ∘ φ) atTop (𝓝 v) := by
  let : Fact ((2:ℝ≥0∞)≠∞) := ⟨by norm_num⟩
  obtain ⟨v,hv,φ,hφ,hw⟩ := bounded_hilbert_weak_subsequence u C hb
  have hd : CauchySeq (fun n => (𝓕 (u (φ n)) : Lp ℂ 2 (volume:Measure E))) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hδ : 0<ε/8 := by positivity
    obtain ⟨s,hs,hμ,hsp⟩ := hspace (ε/8) hδ
    obtain ⟨t,ht,hν,hfr⟩ := hfreq (ε/8) hδ
    have hconv := fourier_double_cut_tendsto s t hs ht hμ hν (u ∘ φ) v C
      (fun n => hb (φ n)) hw
    have hloc := hconv.eventually (Metric.ball_mem_nhds _ hδ)
    have hsp' := hφ.tendsto_atTop.eventually hsp
    have hfr' := hφ.tendsto_atTop.eventually hfr
    obtain ⟨N,hN⟩ := eventually_atTop.mp ((hloc.and hsp').and hfr')
    refine ⟨N,?_⟩
    intro j hj k hk
    obtain ⟨⟨hlj,hsj⟩,hfj⟩ := hN j hj
    obtain ⟨⟨hlk,hsk⟩,hfk⟩ := hN k hk
    have hjj := double_cut_approximation s t hs ht (u (φ j))
    have hkk := double_cut_approximation s t hs ht (u (φ k))
    change dist (cutL2 t ht (𝓕 (cutL2 s hs (u (φ j)))))
      (cutL2 t ht (𝓕 (cutL2 s hs v))) < ε/8 at hlj
    change dist (cutL2 t ht (𝓕 (cutL2 s hs (u (φ k)))))
      (cutL2 t ht (𝓕 (cutL2 s hs v))) < ε/8 at hlk
    have hh := dist_triangle4 (𝓕 (u (φ j)))
      (cutL2 t ht (𝓕 (cutL2 s hs (u (φ j)))) )
      (cutL2 t ht (𝓕 (cutL2 s hs (u (φ k)))) ) (𝓕 (u (φ k)))
    have hmid := dist_triangle (cutL2 t ht (𝓕 (cutL2 s hs (u (φ j)))))
      (cutL2 t ht (𝓕 (cutL2 s hs v)))
      (cutL2 t ht (𝓕 (cutL2 s hs (u (φ k)))))
    rw [dist_comm (cutL2 t ht (𝓕 (cutL2 s hs v)))] at hmid
    rw [dist_comm (cutL2 t ht (𝓕 (cutL2 s hs (u (φ k)))))] at hh
    simp only [dist_eq_norm] at hh hmid hlj hlk ⊢
    linarith
  obtain ⟨w,hw⟩ := cauchySeq_tendsto_of_complete hd
  refine ⟨(Lp.fourierTransformₗᵢ E ℂ).symm w,φ,hφ,?_⟩
  have h := ((Lp.fourierTransformₗᵢ E ℂ).symm.continuous.tendsto w).comp hw
  change Tendsto (fun n => (Lp.fourierTransformₗᵢ E ℂ).symm
    ((Lp.fourierTransformₗᵢ E ℂ) (u (φ n)))) atTop (𝓝 ((Lp.fourierTransformₗᵢ E ℂ).symm w)) at h
  simpa only [LinearIsometryEquiv.symm_apply_apply,Function.comp_def] using h
end Coulomb
end

end
section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology FourierTransform ComplexConjugate ContDiff BigOperators
noncomputable section
namespace Coulomb
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
lemma l2_real_test_inner (f:E → ℝ) (hf:MemLp (fun x => (f x:ℂ)) 2 volume)
    (u:Lp ℂ 2 (volume:Measure E)) :
    inner ℂ (hf.toLp (fun x => (f x:ℂ))) u = ∫ x,(f x:ℂ)*u x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp [hx,RCLike.inner_apply,mul_comm]
lemma weak_l2_pairing_tendsto {u:ℕ → Lp ℂ 2 (volume:Measure E)}
    {v:Lp ℂ 2 (volume:Measure E)}
    (hw:∀ w,Tendsto (fun n => inner ℂ w (u n)) atTop (𝓝 (inner ℂ w v)))
    (f:E → ℝ) (hf:MemLp (fun x => (f x:ℂ)) 2 volume) :
    Tendsto (fun n => ∫ x,(f x:ℂ)*u n x) atTop (𝓝 (∫ x,(f x:ℂ)*v x)) := by
  simpa only [l2_real_test_inner] using hw (hf.toLp (fun x => (f x:ℂ)))
lemma weak_l2_derivative_limit {u d:ℕ → Lp ℂ 2 (volume:Measure E)}
    {v g:Lp ℂ 2 (volume:Measure E)} (a:E)
    (hu:∀ w,Tendsto (fun n => inner ℂ w (u n)) atTop (𝓝 (inner ℂ w v)))
    (hd:∀ w,Tendsto (fun n => inner ℂ w (d n)) atTop (𝓝 (inner ℂ w g)))
    (hw:∀ n (φ:E → ℝ),ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,(fderiv ℝ φ x a:ℂ)*u n x)=-(∫ x,(φ x:ℂ)*d n x)) :
    ∀ (φ:E → ℝ),ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,(fderiv ℝ φ x a:ℂ)*v x)=-(∫ x,(φ x:ℂ)*g x) := by
  intro φ hφ hc
  have hfc : Continuous (fun x => (φ x:ℂ)) := Complex.continuous_ofReal.comp hφ.continuous
  have hfs : HasCompactSupport (fun x => (φ x:ℂ)) := hc.comp_left (g:=fun t:ℝ=>(t:ℂ)) (by simp)
  have hdc : Continuous (fun x => (fderiv ℝ φ x a:ℂ)) :=
    Complex.continuous_ofReal.comp ((hφ.continuous_fderiv_apply (by norm_num)).comp
      (continuous_id.prodMk continuous_const))
  have hds : HasCompactSupport (fun x => (fderiv ℝ φ x a:ℂ)) :=
    ((hc.fderiv ℝ).comp_left (g:=fun T:E →L[ℝ] ℝ => T a) (by simp)).comp_left
      (g:=fun t:ℝ=>(t:ℂ)) (by simp)
  have H1 := weak_l2_pairing_tendsto hu _ (hdc.memLp_of_hasCompactSupport hds)
  have H2 := (weak_l2_pairing_tendsto hd _ (hfc.memLp_of_hasCompactSupport hfs)).neg
  exact tendsto_nhds_unique H1 (by simpa only [hw _ φ hφ hc] using H2)

variable {ι:Type*} [Fintype ι] [DecidableEq ι]

lemma h1_spatial_tight_subsequence
    (u:ℕ → Lp ℂ 2 (volume:Measure (EuclideanSpace ℝ ι)))
    (d:ℕ → ι → Lp ℂ 2 (volume:Measure (EuclideanSpace ℝ ι)))
    (hw:∀ n i (φ:EuclideanSpace ℝ ι → ℝ),ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,(fderiv ℝ φ x (EuclideanSpace.single i 1):ℂ)*u n x)=-(∫ x,(φ x:ℂ)*d n i x))
    (C K:ℝ) (hb:∀ n,‖u n‖≤C) (hK:∀ n,∑ i,‖d n i‖^2≤K)
    (hsp:∀ ε:ℝ,0<ε → ∃ s:Set (EuclideanSpace ℝ ι),∃ hs:MeasurableSet s,volume s≠(⊤:ℝ≥0∞) ∧
      ∀ᶠ n in atTop,‖cutL2 sᶜ hs.compl (u n)‖≤ε) :
    ∃ v:Lp ℂ 2 (volume:Measure (EuclideanSpace ℝ ι)),∃ φ:ℕ → ℕ,StrictMono φ ∧
      Tendsto (u ∘ φ) atTop (𝓝 v) := by
  apply l2_tight_frequency_subsequence u C hb hsp
  intro ε hε
  obtain ⟨R,hR,H⟩ := bounded_gradient_frequency_tight u d hw K hK ε hε
  exact ⟨Metric.ball 0 R,measurableSet_ball,measure_ball_lt_top.ne,Filter.Eventually.of_forall H⟩
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_L2MultiplierContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexConjugate BigOperators
noncomputable section
namespace Coulomb
variable {X:Type*} [MeasurableSpace X] {μ:Measure X}
lemma real_multiplier_inner (f:X → ℝ) (u v U V:Lp ℂ 2 μ)
    (hu:(U:X → ℂ)=ᵐ[μ]fun x => (f x:ℂ)*u x)
    (hv:(V:X → ℂ)=ᵐ[μ]fun x => (f x:ℂ)*v x) :
    inner ℂ v U=inner ℂ V u := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu,hv] with x hx hy
  simp only [RCLike.inner_apply,hx,hy,map_mul,Complex.conj_ofReal]
  ring
lemma real_multiplier_quadratic (f:X → ℝ) (u U:Lp ℂ 2 μ)
    (hu:(U:X → ℂ)=ᵐ[μ]fun x => (f x:ℂ)*u x) :
    (inner ℂ u U).re=∫ x,f x*‖u x‖^2 ∂μ := by
  rw [L2.inner_def]
  change RCLike.re (∫ x,inner ℂ (u x) (U x) ∂μ)=_
  rw [←integral_re (L2.integrable_inner (𝕜:=ℂ) u U)]
  apply integral_congr_ae
  filter_upwards [hu] with x hx
  rw [hx]
  change (((f x:ℂ)*u x)*conj (u x)).re=f x*‖u x‖^2
  rw [mul_assoc,Complex.mul_conj]
  simp [Complex.normSq_eq_norm_sq,-Complex.ofReal_pow]

lemma real_multiplier_quadratic_diff_bound (f:X → ℝ) (u v U V:Lp ℂ 2 μ)
    (hu:(U:X → ℂ)=ᵐ[μ]fun x => (f x:ℂ)*u x)
    (hv:(V:X → ℂ)=ᵐ[μ]fun x => (f x:ℂ)*v x) :
    |(inner ℂ u U).re-(inner ℂ v V).re|≤(‖U‖+‖V‖)*‖u-v‖ := by
  have he : inner ℂ u U-inner ℂ v V=inner ℂ (u-v) U+inner ℂ V (u-v) := by
    rw [inner_sub_left,inner_sub_right,←real_multiplier_inner f u v U V hu hv,
      ←real_multiplier_inner f v v V V hv hv]
    abel
  calc
    |(inner ℂ u U).re-(inner ℂ v V).re|=|(inner ℂ u U-inner ℂ v V).re|:=rfl
    _ ≤ ‖inner ℂ u U-inner ℂ v V‖ := Complex.abs_re_le_norm _
    _ ≤ ‖inner ℂ (u-v) U‖+‖inner ℂ V (u-v)‖ := by rw [he]; exact norm_add_le _ _
    _ ≤ ‖u-v‖*‖U‖+‖V‖*‖u-v‖ := add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ = (‖U‖+‖V‖)*‖u-v‖ := by ring
lemma real_multiplier_quadratic_tendsto (f:X → ℝ) (u:ℕ → Lp ℂ 2 μ) (v:Lp ℂ 2 μ)
    (U:ℕ → Lp ℂ 2 μ) (V:Lp ℂ 2 μ)
    (hu:∀ k,(U k:X → ℂ)=ᵐ[μ]fun x => (f x:ℂ)*u k x)
    (hv:(V:X → ℂ)=ᵐ[μ]fun x => (f x:ℂ)*v x)
    (hconv:Tendsto u atTop (𝓝 v)) (C:ℝ) (hC:∀ k,‖U k‖≤C) :
    Tendsto (fun k => ∫ x,f x*‖u k x‖^2 ∂μ) atTop (𝓝 (∫ x,f x*‖v x‖^2 ∂μ)) := by
  simp_rw [←real_multiplier_quadratic f _ _ hv]
  have H:Tendsto (fun k => (inner ℂ (u k) (U k)).re-(inner ℂ v V).re) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a:=fun k => (C+‖V‖)*‖u k-v‖)
    · intro k
      exact (real_multiplier_quadratic_diff_bound f (u k) v (U k) V (hu k) hv).trans
        (mul_le_mul_of_nonneg_right (add_le_add (hC k) (le_refl ‖V‖)) (norm_nonneg _))
    · have h:=((hconv.sub_const v).norm.const_mul (C+‖V‖))
      simpa using h
  have he: Tendsto (fun k => (inner ℂ (u k) (U k)).re) atTop (𝓝 (inner ℂ v V).re) :=
    (tendsto_sub_nhds_zero_iff).mp H
  simpa only [real_multiplier_quadratic f _ _ (hu _)] using he
end Coulomb
end

end
section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexConjugate BigOperators
noncomputable section
namespace Coulomb
variable {n:ℕ}
lemma H1Vector.hardyMultiplier_ae (u:H1Vector n) (s:Spins n) (i:Fin n) (R:HardyCoordinates n i) :
    (u.hardyMultiplier s i R:Configuration n → ℂ)=ᵐ[volume]fun x => (hardyCoulomb i R x:ℂ)*u.valueL2 s x :=
  (u.hardy_multiplier_memLp s i R).coeFn_toLp
lemma H1Vector.hardyMultiplier_norm_sq (u:H1Vector n) (s:Spins n) (i:Fin n) (R:HardyCoordinates n i) :
    ‖u.hardyMultiplier s i R‖^2≤8*kinetic u := by
  rw [l2_norm_sq_integral]
  have he:(∫ x,‖u.hardyMultiplier s i R x‖^2)=∫ x,(blockRadiusSq i R x)⁻¹*‖u.value s x‖^2 := by
    apply integral_congr_ae
    filter_upwards [u.hardyMultiplier_ae s i R,u.valueL2_ae s] with x hx hy
    simp only [hx,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,hardyCoulomb_sq,hy]
  rw [he]
  have hs:(∑ b:Fin 3,∫ x,‖u.gradient s (i,b) x‖^2)≤∑ a:Fin n × Fin 3,∫ x,‖u.gradient s a x‖^2 := by
    rw [Fintype.sum_prod_type]
    exact Finset.single_le_sum (f:=fun j:Fin n => ∑ b:Fin 3,∫ x:Configuration n,‖u.gradient s (j,b) x‖^2)
      (fun j _ => Finset.sum_nonneg fun b _ => integral_nonneg fun x => sq_nonneg _) (Finset.mem_univ i)
  have ht:(∑ a,∫ x,‖u.gradient s a x‖^2)≤∑ t,∑ a,∫ x,‖u.gradient t a x‖^2 :=
    Finset.single_le_sum (f:=fun t:Spins n => ∑ a:Fin n × Fin 3,∫ x:Configuration n,‖u.gradient t a x‖^2)
      (fun t _ => Finset.sum_nonneg fun a _ => integral_nonneg fun x => sq_nonneg _) (Finset.mem_univ s)
  have hh:=(u.hardy s i R).2
  unfold kinetic
  linarith
lemma H1Vector.hardyMultiplier_norm_le (u:H1Vector n) (s:Spins n) (i:Fin n) (R:HardyCoordinates n i)
    {K:ℝ} (hK:kinetic u≤K) : ‖u.hardyMultiplier s i R‖≤Real.sqrt (8*K) := by
  have hp:0≤8*K:=mul_nonneg (by norm_num) ((kinetic_nonneg u).trans hK)
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hp]
  exact (u.hardyMultiplier_norm_sq s i R).trans (mul_le_mul_of_nonneg_left hK (by norm_num))
lemma hardy_form_strong_tendsto (u:ℕ → H1Vector n) (v:H1Vector n) (s:Spins n) (i:Fin n) (R:HardyCoordinates n i)
    (hv:Tendsto (fun k => (u k).valueL2 s) atTop (𝓝 (v.valueL2 s)))
    (K:ℝ) (hK:∀ k,kinetic (u k)≤K) :
    Tendsto (fun k => ∫ x,hardyCoulomb i R x*‖(u k).value s x‖^2) atTop
      (𝓝 (∫ x,hardyCoulomb i R x*‖v.value s x‖^2)) := by
  have H:=real_multiplier_quadratic_tendsto (hardyCoulomb i R)
    (fun k => (u k).valueL2 s) (v.valueL2 s)
    (fun k => (u k).hardyMultiplier s i R) (v.hardyMultiplier s i R)
    (fun k => (u k).hardyMultiplier_ae s i R) (v.hardyMultiplier_ae s i R) hv
    (Real.sqrt (8*K)) (fun k => (u k).hardyMultiplier_norm_le s i R (hK k))
  have he(w:H1Vector n) : (∫ x,hardyCoulomb i R x*‖w.valueL2 s x‖^2)=
      ∫ x,hardyCoulomb i R x*‖w.value s x‖^2 := by
    apply integral_congr_ae
    filter_upwards [w.valueL2_ae s] with x hx
    rw [hx]
  simpa only [he] using H
end Coulomb
end

end
section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexConjugate ContDiff BigOperators
noncomputable section
namespace Coulomb
lemma h1_bounded_tight_compact {n:ℕ} (u:ℕ → H1Vector n) (K:ℝ)
    (hm:∀ k,mass (u k)=1) (hk:∀ k,kinetic (u k)≤K)
    (hsp:∀ ε:ℝ,0<ε → ∃ A:Set (Configuration n),∃ hA:MeasurableSet A,volume A≠(⊤:ℝ≥0∞) ∧
      ∀ᶠ k in atTop,∀ s,‖cutL2 Aᶜ hA.compl ((u k).valueL2 s)‖≤ε) :
    ∃ v:H1Vector n,mass v=1 ∧ kinetic v≤K ∧ ∃ φ:ℕ → ℕ,StrictMono φ ∧
      (∀ s,Tendsto (fun k => (u (φ k)).valueL2 s) atTop (𝓝 (v.valueL2 s))) ∧
      (∀ s a w,Tendsto (fun k => inner ℂ w ((u (φ k)).gradientL2 s a)) atTop
        (𝓝 (inner ℂ w (v.gradientL2 s a)))) := by
  let : Fact ((2:ℝ≥0∞)≠(⊤:ℝ≥0∞)) := ⟨by norm_num⟩
  have hK:0≤K := (kinetic_nonneg (u 0)).trans (hk 0)
  have huv (k:ℕ) (s:Spins n) : ‖(u k).valueL2 s‖≤1 := by
    have H:=hm k
    rw [H1Vector.mass_eq_norm] at H
    have hh:=Finset.single_le_sum (fun t _ => sq_nonneg ‖(u k).valueL2 t‖) (Finset.mem_univ s)
    nlinarith [norm_nonneg ((u k).valueL2 s)]
  have hgrad (k:ℕ) : ∑ s,∑ a,‖(u k).gradientL2 s a‖^2≤2*K := by
    have H:=hk k
    rw [H1Vector.kinetic_eq_norm] at H
    linarith
  have hgs (k:ℕ) (s:Spins n) : ∑ a,‖(u k).gradientL2 s a‖^2≤2*K :=
    (Finset.single_le_sum (fun t _ => Finset.sum_nonneg fun a _ => sq_nonneg _) (Finset.mem_univ s)).trans (hgrad k)
  obtain ⟨v0,φ,hφ,hv0⟩ := finite_simultaneous_subsequence (fun k s => (u k).valueL2 s) (by
    intro s φ hφ
    apply h1_spatial_tight_subsequence (fun k => (u (φ k)).valueL2 s)
      (fun k a => (u (φ k)).gradientL2 s a) (fun k a => (u (φ k)).weak_partial_L2 s a)
      1 (2*K) (fun k => huv (φ k) s) (fun k => hgs (φ k) s)
    intro ε hε
    obtain ⟨A,hA,hfin,H⟩:=hsp ε hε
    exact ⟨A,hA,hfin,(hφ.tendsto_atTop.eventually H).mono (fun k hk => hk s)⟩)
  let g0:ℕ → (Spins n × (Fin n × Fin 3)) → Lp ℂ 2 (volume:Measure (Configuration n)) :=
    fun k sa => (u (φ k)).gradientL2 sa.1 sa.2
  obtain ⟨g,hg,ψ,hψ,hw⟩:=bounded_finite_hilbert_weak_subsequence g0 (2*K) (by
    intro k
    simpa only [Fintype.sum_prod_type,g0] using hgrad (φ k))
  have hv(s:Spins n) : Tendsto (fun k => (u (φ (ψ k))).valueL2 s) atTop (𝓝 (v0 s)) :=
    (hv0 s).comp hψ.tendsto_atTop
  have hweak(s:Spins n) (a:Fin n × Fin 3) : ∀ (f:Configuration n → ℝ),ContDiff ℝ ∞ f → HasCompactSupport f →
      (∫ x,(fderiv ℝ f x (EuclideanSpace.single a 1):ℂ)*v0 s x)=-(∫ x,(f x:ℂ)*g (s,a) x) := by
    apply weak_l2_derivative_limit (EuclideanSpace.single a 1)
      (fun w => tendsto_const_nhds.inner (hv s)) (hw (s,a))
    exact fun k => (u (φ (ψ k))).weak_partial_L2 s a
  let v:=H1Vector.ofL2 v0 (fun s a => g (s,a)) hweak
  have hvv(s:Spins n) : v.valueL2 s=v0 s := H1Vector.ofL2_valueL2 ..
  have hvg(s:Spins n) (a:Fin n × Fin 3) : v.gradientL2 s a=g (s,a) := H1Vector.ofL2_gradientL2 ..
  refine ⟨v,?_,?_,φ ∘ ψ,hφ.comp hψ,?_,?_⟩
  · have H:Tendsto (fun k => ∑ s,‖(u (φ (ψ k))).valueL2 s‖^2) atTop (𝓝 (∑ s,‖v0 s‖^2)):=
      tendsto_finsetSum _ (fun s _ => (hv s).norm.pow 2)
    have he (k:ℕ) : (∑ s,‖(u (φ (ψ k))).valueL2 s‖^2)=1 := by
      rw [←H1Vector.mass_eq_norm]; exact hm _
    rw [H1Vector.mass_eq_norm]
    simp_rw [hvv]
    exact tendsto_nhds_unique H (by simp only [he]; exact tendsto_const_nhds)
  · rw [H1Vector.kinetic_eq_norm]
    simp_rw [hvg]
    rw [Fintype.sum_prod_type] at hg
    linarith
  · intro s
    simpa only [hvv,Function.comp_def] using hv s
  · intro s a w
    simpa only [hvg,Function.comp_def,g0] using hw (s,a) w
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_H1EnergyLimit
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexConjugate BigOperators
noncomputable section
namespace Coulomb
lemma pairEnergy_eq_sum {n:ℕ} (u:H1Vector n) :
    pairEnergy u=∑ s,∑ i,∑ j,if i<j then (∫ x,coulombKernel (position x i-position x j)*‖u.value s x‖^2) else 0 := by
  unfold pairEnergy
  apply Finset.sum_congr rfl
  intro s _
  simp only [Finset.sum_mul,ite_mul,zero_mul]
  have hi(i j:Fin n) : Integrable (fun x => if i<j then coulombKernel (position x i-position x j)*‖u.value s x‖^2 else 0) := by
    split_ifs with h
    · exact (u.pair_coulomb_integrable_bound s i j (ne_of_lt h) (by norm_num : (0:ℝ)<1)).1
    · simp
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp_all

lemma nuclearEnergy_strong_tendsto {M n:ℕ} (S:Nuclei M) (u:ℕ → H1Vector n) (v:H1Vector n)
    (hv:∀ s,Tendsto (fun k => (u k).valueL2 s) atTop (𝓝 (v.valueL2 s)))
    (K:ℝ) (hK:∀ k,kinetic (u k)≤K) :
    Tendsto (fun k => nuclearEnergy S (u k)) atTop (𝓝 (nuclearEnergy S v)) := by
  simp only [nuclearEnergy_eq_sum]
  apply tendsto_finsetSum
  intro s _
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  apply Tendsto.const_mul
  simpa only [hardyCoulomb_nuclear] using hardy_form_strong_tendsto u v s i (nuclearHardyCoordinates i (S.position j)) (hv s) K hK

lemma pairEnergy_strong_tendsto {n:ℕ} (u:ℕ → H1Vector n) (v:H1Vector n)
    (hv:∀ s,Tendsto (fun k => (u k).valueL2 s) atTop (𝓝 (v.valueL2 s)))
    (K:ℝ) (hK:∀ k,kinetic (u k)≤K) :
    Tendsto (fun k => pairEnergy (u k)) atTop (𝓝 (pairEnergy v)) := by
  simp only [pairEnergy_eq_sum]
  apply tendsto_finsetSum
  intro s _
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  by_cases h:i<j
  · simp only [ite_eq_left h]
    simpa only [hardyCoulomb_pair] using hardy_form_strong_tendsto u v s i (pairHardyCoordinates i j (ne_of_lt h)) (hv s) K hK
  · simp only [ite_eq_right h]; exact tendsto_const_nhds

lemma finite_weak_norm_sq_le_of_tendsto {ι H:Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (u:ℕ → ι → H) (v:ι → H) (L:ℝ)
    (hw:∀ i w,Tendsto (fun k => inner ℂ w (u k i)) atTop (𝓝 (inner ℂ w (v i))))
    (hL:Tendsto (fun k => ∑ i,‖u k i‖^2) atTop (𝓝 L)) : ∑ i,‖v i‖^2≤L := by
  let U:ℕ → PiLp 2 (fun _:ι => H):=fun k => WithLp.toLp 2 (u k)
  let V:PiLp 2 (fun _:ι => H):=WithLp.toLp 2 v
  have hL0:0≤L := ge_of_tendsto hL (Eventually.of_forall fun k => Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hW:∀ W:PiLp 2 (fun _:ι => H),Tendsto (fun k => inner ℂ W (U k)) atTop (𝓝 (inner ℂ W V)) := by
    intro W
    simp only [PiLp.inner_apply,U,V]
    exact tendsto_finsetSum _ (fun i _ => hw i (W i))
  apply le_of_forall_pos_le_add
  intro ε hε
  have hU:∀ᶠ k in atTop,‖U k‖≤Real.sqrt (L+ε) := by
    filter_upwards [hL.eventually (gt_mem_nhds (show L<L+ε by linarith))] with k hk
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2,Real.sq_sqrt (by positivity)]
    exact hk.le
  have hV:=weak_tendsto_norm_le (Real.sqrt_nonneg (L+ε)) hW hU
  have H:=pow_le_pow_left₀ (norm_nonneg _) hV 2
  rw [Real.sq_sqrt (by positivity),PiLp.norm_sq_eq_of_L2] at H
  exact H

lemma form_strong_weak_limit_le {M n:ℕ} (S:Nuclei M) (u:ℕ → H1Vector n) (v:H1Vector n)
    (hv:∀ s,Tendsto (fun k => (u k).valueL2 s) atTop (𝓝 (v.valueL2 s)))
    (hw:∀ s a w,Tendsto (fun k => inner ℂ w ((u k).gradientL2 s a)) atTop
      (𝓝 (inner ℂ w (v.gradientL2 s a))))
    (K:ℝ) (hK:∀ k,kinetic (u k)≤K) (E:ℝ)
    (hE:Tendsto (fun k => form S (u k)) atTop (𝓝 E)) : form S v≤E := by
  let : Fact ((2:ℝ≥0∞)≠(⊤:ℝ≥0∞)) := ⟨by norm_num⟩
  have hkin:Tendsto (fun k => kinetic (u k)) atTop (𝓝 (E+nuclearEnergy S v-pairEnergy v)) := by
    convert (hE.add (nuclearEnergy_strong_tendsto S u v hv K hK)).sub (pairEnergy_strong_tendsto u v hv K hK) using 1
    all_goals try with_reducible_and_instances rfl
    ext k; unfold form; ring
  have H:=finite_weak_norm_sq_le_of_tendsto
    (fun k (sa:Spins n × (Fin n × Fin 3)) => (u k).gradientL2 sa.1 sa.2)
    (fun sa => v.gradientL2 sa.1 sa.2) (2*(E+nuclearEnergy S v-pairEnergy v))
    (fun sa => hw sa.1 sa.2) (by
      convert hkin.const_mul 2 using 1
      all_goals try with_reducible_and_instances rfl
      ext k
      rw [H1Vector.kinetic_eq_norm,Fintype.sum_prod_type]
      ring)
  rw [Fintype.sum_prod_type] at H
  rw [form,H1Vector.kinetic_eq_norm]
  linarith
end Coulomb
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
namespace Coulomb
lemma atom_sector_trial_approx (Z:ℕ) (hZ:1 ≤ Z) (n:ℕ) (E:ℝ)
    (hE:(E:EReal)=sectorFormBottom (atom Z hZ) n) {ε:ℝ} (hε:0<ε) :
    ∃ u:H1Vector n,Antisymmetric u ∧ mass u=1 ∧ form (atom Z hZ) u<E+ε := by
  have hh:sectorFormBottom (atom Z hZ) n<(E+ε:EReal) := by
    rw [←hE]; exact EReal.coe_lt_coe_iff.mpr (by linarith)
  obtain ⟨e,he,helt⟩:=sInf_lt_iff.mp hh
  obtain ⟨u,ha,hm,rfl⟩:=he
  exact ⟨u,ha,hm,EReal.coe_lt_coe_iff.mp helt⟩

lemma kinetic_bound_of_form_bound {M n:ℕ} (S:Nuclei M) (u:H1Vector n) :
    kinetic u ≤ 2*form S u+8*(n:ℝ)*(totalCharge S)^2*mass u := by
  let η:ℝ:=1/(16*totalCharge S)
  have hZ:=totalCharge_pos S
  have hη:0<η := by dsimp [η]; positivity
  have H:=nuclearEnergy_bound S u hη
  have h1:8*η*totalCharge S=(1/2:ℝ) := by dsimp [η]; field_simp; ring
  have h2:(n:ℝ)*totalCharge S/(4*η)=4*(n:ℝ)*(totalCharge S)^2 := by dsimp [η]; field_simp; ring
  rw [h1,h2] at H
  have hp:=pairEnergy_nonneg u
  unfold form
  linarith

lemma atom_normalized_form_ge_bottom (Z:ℕ) (hZ:1 ≤ Z) {n:ℕ} (u:H1Vector n)
    (ha:Antisymmetric u) (hm:mass u=1) (E:ℝ) (hE:(E:EReal) ≤ sectorFormBottom (atom Z hZ) n) :
    E ≤ form (atom Z hZ) u :=
  EReal.coe_le_coe_iff.mp (hE.trans (sInf_le ⟨u,ha,hm,rfl⟩))

lemma atom_minimizing_sequence (Z:ℕ) (hZ:1 ≤ Z) (n:ℕ) (E:ℝ)
    (hE:(E:EReal)=sectorFormBottom (atom Z hZ) n) :
    ∃ u:ℕ → H1Vector n,(∀ k,Antisymmetric (u k)) ∧ (∀ k,mass (u k)=1) ∧
      (∀ k,kinetic (u k) ≤ 2*(E+1)+8*(n:ℝ)*(Z:ℝ)^2) ∧
      Tendsto (fun k => form (atom Z hZ) (u k)) atTop (𝓝 E) := by
  choose u ha hm hf using fun k:ℕ => atom_sector_trial_approx Z hZ n E hE (show 0<(1:ℝ)/(k+1) by positivity)
  refine ⟨u,ha,hm,?_,?_⟩
  · intro k
    have H:=kinetic_bound_of_form_bound (atom Z hZ) (u k)
    have htotal:totalCharge (atom Z hZ)=(Z:ℝ) := by simp [totalCharge,atom]
    rw [hm k,htotal,mul_one] at H
    have hsmall:(1:ℝ)/(k+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) k])
    linarith [hf k]
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (show Tendsto (fun k:ℕ => E+1/((k:ℝ)+1)) atTop (𝓝 E) from by
        simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)))
    · intro k; exact atom_normalized_form_ge_bottom Z hZ (u k) (ha k) (hm k) E hE.le
    · exact fun k => (hf k).le
end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_SpectralTheory_StrictBinding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical
noncomputable section
namespace Coulomb

lemma atom_strict_binding_attained_oai (Z:ℕ) (hZ:1 ≤ Z) {n:ℕ} (hn:0<n)
    (hstrict:sectorFormBottom (atom Z hZ) n < sectorFormBottom (atom Z hZ) (n-1)) :
    ∃ u:H1Vector n,Antisymmetric u ∧ mass u=1 ∧
      (form (atom Z hZ) u:EReal)=sectorFormBottom (atom Z hZ) n := by
  let E:ℝ:=(sectorFormBottom (atom Z hZ) n).toReal
  let P:ℝ:=(sectorFormBottom (atom Z hZ) (n-1)).toReal
  have hE:(E:EReal)=sectorFormBottom (atom Z hZ) n:=atom_sectorFormBottom_real Z hZ n
  have hP:(P:EReal)=sectorFormBottom (atom Z hZ) (n-1):=atom_sectorFormBottom_real Z hZ (n-1)
  have hgap:E<P := EReal.coe_lt_coe_iff.mp (by rwa [hE,hP])
  obtain ⟨u,ha,hm,hk,hlim⟩:=atom_minimizing_sequence Z hZ n E hE
  obtain ⟨v,hvm,hvk,φ,hφ,hv,hw⟩:=h1_bounded_tight_compact u _ hm hk
    (strictly_bound_sequence_tight Z hZ hn u ha hm E P hE.le hP.le hgap hlim)
  have hva:Antisymmetric v := antisymmetric_strong_limit (fun k => u (φ k)) v (fun k => ha (φ k)) hv
  have hupper:=form_strong_weak_limit_le (atom Z hZ) (fun k => u (φ k)) v hv hw _ (fun k => hk (φ k)) E (hlim.comp hφ.tendsto_atTop)
  have hlower:=atom_normalized_form_ge_bottom Z hZ v hva hvm E hE.le
  refine ⟨v,hva,hvm,?_⟩
  rw [le_antisymm hupper hlower,hE]
end Coulomb
end

end

end OAI
end

theorem solution : type_of% @OAI.Coulomb.atom_strict_binding_attained_oai := @OAI.Coulomb.atom_strict_binding_attained_oai
