-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.inducedE_inducedCoeff_inv_eq_of_not_isBadPlace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ef247772-5af3-5b81-9a7b-7b6a0ca18b78

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_inducedE_inducedCoeff_inv_eq_of_not_isBadPlace

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal NumberField.InfinitePlace LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction

open Polynomial NumberField.TateGlobal

noncomputable section

namespace Ws47
namespace ContraParams

theorem prod_reflect {R : Type*} [CommSemiring R] {ι : Type*} (s : Finset ι) (Q : ι → R[X]) (f : ι → ℕ)
    (h : ∀ i ∈ s, (Q i).natDegree ≤ f i) :
    ∏ i ∈ s, reflect (f i) (Q i) = reflect (∑ i ∈ s, f i) (∏ i ∈ s, Q i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty, Finset.prod_empty, Finset.sum_empty, ← C_1, reflect_C, pow_zero, mul_one]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha,
        reflect_mul _ _ (h a (Finset.mem_insert_self a s))
          ((natDegree_prod_le _ _).trans (Finset.sum_le_sum fun i hi => h i (Finset.mem_insert_of_mem hi))),
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))]

theorem norm_coeff_prod_le {ι : Type*} (s : Finset ι) (p : ι → ℂ[X]) (P : ι → ℝ[X])
    (h : ∀ i ∈ s, ∀ k, ‖(p i).coeff k‖ ≤ (P i).coeff k) (k : ℕ) :
    ‖(∏ i ∈ s, p i).coeff k‖ ≤ (∏ i ∈ s, P i).coeff k := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
      rw [Finset.prod_empty, Finset.prod_empty, coeff_one, coeff_one]
      split_ifs <;> simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, coeff_mul, coeff_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
      refine (norm_mul_le _ _).trans ?_
      exact mul_le_mul (h a (Finset.mem_insert_self a s) _)
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) _) (norm_nonneg _)
        ((norm_nonneg _).trans (h a (Finset.mem_insert_self a s) _))

theorem norm_coeff_factor_le (c : ℂ) (hc : ‖c‖ ≤ 1) (f : ℕ) (hf : f ≠ 0) (k : ℕ) :
    ‖(C 1 - C c * X ^ f : ℂ[X]).coeff k‖ ≤ ((1 + X : ℝ[X]) ^ f).coeff k := by
  rw [coeff_one_add_X_pow, coeff_sub, coeff_C, coeff_C_mul, coeff_X_pow]
  by_cases hk0 : k = 0
  · subst hk0
    simp [Ne.symm hf]
  · by_cases hkf : k = f
    · subst hkf
      simp [hk0, hc]
    · simp [hk0, hkf]

end Ws47.ContraParams

open Ws47.ContraParams in

theorem solution
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ IsBadPlace K μ v) :
    inducedE3 ℚ (inducedCoeff K μ) v ≠ 0 ∧
    ‖inducedE3 ℚ (inducedCoeff K μ) v‖ = 1 ∧
    inducedE1 ℚ (inducedCoeff K μ⁻¹) v = inducedE2 ℚ (inducedCoeff K μ) v * (inducedE3 ℚ (inducedCoeff K μ) v)⁻¹ ∧
    inducedE2 ℚ (inducedCoeff K μ⁻¹) v = inducedE1 ℚ (inducedCoeff K μ) v * (inducedE3 ℚ (inducedCoeff K μ) v)⁻¹ ∧
    inducedE3 ℚ (inducedCoeff K μ⁻¹) v = (inducedE3 ℚ (inducedCoeff K μ) v)⁻¹ ∧
    ‖inducedE1 ℚ (inducedCoeff K μ⁻¹) v‖ ≤ 3 ∧ ‖inducedE2 ℚ (inducedCoeff K μ⁻¹) v‖ ≤ 3 ∧
    ‖inducedE3 ℚ (inducedCoeff K μ⁻¹) v‖ ≤ 1 := by
  classical

  have huniq : ∀ f g : 𝓞 ℚ →+* 𝓞 K, f = g := fun f g => by
    have h := RingHom.ext_int (f.comp Rat.ringOfIntegersEquiv.symm.toRingHom)
      (g.comp Rat.ringOfIntegersEquiv.symm.toRingHom)
    refine RingHom.ext fun x => ?_
    obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective x
    exact DFunLike.congr_fun h n
  have hinst : ‹Algebra (𝓞 ℚ) (𝓞 K)› = inst_ringOfIntegersAlgebra ℚ K :=
    Algebra.algebra_ext _ _ fun r => DFunLike.congr_fun (huniq _ _) r
  subst hinst
  haveI : v.asIdeal.IsMaximal := v.isMaximal

  have hunit : IsUnitaryChar (𝓞 K) K μ := hμ.2.2
  have hram : ∀ w ∈ primeFibre ℚ K v, v.asIdeal.ramificationIdx' w.asIdeal = 1 := by
    intro w hw
    by_contra h
    exact hv (Or.inl ⟨w, hw, h⟩)
  have hunr : ∀ w ∈ primeFibre ℚ K v, IsUnramifiedCharAt μ w := by
    intro w hw
    by_contra h
    exact hv (Or.inr ⟨w, hw, h⟩)

  have hc_norm : ∀ w ∈ primeFibre ℚ K v, ‖inducedCoeff K μ w‖ = 1 := by
    intro w hw
    unfold inducedCoeff
    rw [if_pos (hunr w hw)]
    exact hunit _
  have hc_ne : ∀ w ∈ primeFibre ℚ K v, inducedCoeff K μ w ≠ 0 := by
    intro w hw h
    have := hc_norm w hw
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hinv : inducedCoeff K μ⁻¹ = fun w => (inducedCoeff K μ w)⁻¹ := by
    funext w
    have hiff : IsUnramifiedCharAt μ⁻¹ w ↔ IsUnramifiedCharAt μ w := by
      unfold IsUnramifiedCharAt localChar
      simp only [MonoidHom.comp_apply, MonoidHom.inv_apply, inv_eq_one]
    unfold inducedCoeff
    by_cases h : IsUnramifiedCharAt μ w
    · rw [if_pos (hiff.mpr h), if_pos h, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    · rw [if_neg (mt hiff.mp h), if_neg h, _root_.inv_zero]

  have hsub : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∈ primeFibre ℚ K v →
      𝔓.asIdeal ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 K) := by
    intro 𝔓 h𝔓
    rw [mem_primeFibre] at h𝔓
    rw [IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot]
    refine ⟨𝔓.isPrime, (Ideal.liesOver_iff _ _).mpr ?_⟩
    rw [← h𝔓]
    rfl
  have hfin : (primeFibre ℚ K v).Finite :=
    ((IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 K)).finite_toSet.preimage
      (f := fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.asIdeal) (fun a _ b _ h => HeightOneSpectrum.ext h)).subset
      (fun 𝔓 h𝔓 => hsub 𝔓 h𝔓)
  have hS : ∀ w, w ∈ hfin.toFinset ↔ w ∈ primeFibre ℚ K v := fun w => hfin.mem_toFinset

  have hf : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∈ primeFibre ℚ K v →
      (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal = v.asIdeal.inertiaDeg' 𝔓.asIdeal := by
    intro 𝔓 h𝔓; rw [mem_primeFibre] at h𝔓; rw [h𝔓]
  have hfne : ∀ w ∈ hfin.toFinset, v.asIdeal.inertiaDeg' w.asIdeal ≠ 0 := by
    intro w hw
    have hw' := (hS w).mp hw
    haveI : w.asIdeal.LiesOver v.asIdeal :=
      (Ideal.liesOver_iff _ _).mpr (by rw [mem_primeFibre] at hw'; rw [← hw']; rfl)
    exact (Ideal.inertiaDeg'_pos v.asIdeal w.asIdeal).ne'

  have hsum : ∑ w ∈ hfin.toFinset, v.asIdeal.inertiaDeg' w.asIdeal = 3 := by
    have htot : ∑ P ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 K),
        v.asIdeal.ramificationIdx' P * v.asIdeal.inertiaDeg' P = 3 :=
      (Ideal.sum_ramification_inertia (𝓞 K) ℚ K v.ne_bot).trans hdeg
    have himage : hfin.toFinset.image (fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal) =
        IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 K) := by
      ext P
      constructor
      · intro hP
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hP
        exact hsub w ((hS w).mp hw)
      · intro hP
        have hP' := (IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot (𝓞 K)).mp hP
        have hne : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver v.ne_bot hP'
        refine Finset.mem_image.mpr ⟨⟨P, hP'.1, hne⟩, (hS _).mpr ?_, rfl⟩
        rw [mem_primeFibre]
        exact HeightOneSpectrum.ext hP'.2.over.symm
    have hinj : Set.InjOn (fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal) ↑hfin.toFinset :=
      fun a _ b _ h => HeightOneSpectrum.ext h
    rw [← himage, Finset.sum_image hinj] at htot
    rw [← htot]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [hram w ((hS w).mp hw), one_mul]

  have hP : inducedEulerPoly ℚ (inducedCoeff K μ) v =
      ∏ w ∈ hfin.toFinset, (C 1 - C (inducedCoeff K μ w) * X ^ (v.asIdeal.inertiaDeg' w.asIdeal)) := by
    unfold inducedEulerPoly
    rw [finprod_mem_eq_finite_toFinset_prod _ hfin]
    refine Finset.prod_congr rfl fun w hw => ?_
    unfold inducedFactor
    rw [hf w ((hS w).mp hw)]
  have hP' : inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v =
      ∏ w ∈ hfin.toFinset, (C 1 - C (inducedCoeff K μ w)⁻¹ * X ^ (v.asIdeal.inertiaDeg' w.asIdeal)) := by
    unfold inducedEulerPoly
    rw [finprod_mem_eq_finite_toFinset_prod _ hfin]
    refine Finset.prod_congr rfl fun w hw => ?_
    unfold inducedFactor
    rw [hf w ((hS w).mp hw), hinv]

  have hdegQ : ∀ w ∈ hfin.toFinset,
      (C 1 - C (inducedCoeff K μ w) * X ^ (v.asIdeal.inertiaDeg' w.asIdeal) : ℂ[X]).natDegree ≤
        v.asIdeal.inertiaDeg' w.asIdeal := by
    intro w _
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · rw [natDegree_C]; exact Nat.zero_le _
    · exact natDegree_C_mul_X_pow_le _ _

  have hfac : ∀ w ∈ hfin.toFinset,
      (C 1 - C (inducedCoeff K μ w)⁻¹ * X ^ (v.asIdeal.inertiaDeg' w.asIdeal) : ℂ[X]) =
        C (-(inducedCoeff K μ w)⁻¹) *
          reflect (v.asIdeal.inertiaDeg' w.asIdeal)
            (C 1 - C (inducedCoeff K μ w) * X ^ (v.asIdeal.inertiaDeg' w.asIdeal)) := by
    intro w hw
    rw [reflect_sub, reflect_C, reflect_C_mul_X_pow, revAt_le (le_refl _), Nat.sub_self, pow_zero, mul_one,
      map_neg, C_1, one_mul]
    have hut : C (inducedCoeff K μ w)⁻¹ * C (inducedCoeff K μ w) = (1 : ℂ[X]) := by
      rw [← map_mul, inv_mul_cancel₀ (hc_ne w ((hS w).mp hw)), map_one]
    linear_combination -hut

  have hb_ne : ∏ w ∈ hfin.toFinset, -(inducedCoeff K μ w) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun w hw => neg_ne_zero.mpr (hc_ne w ((hS w).mp hw))
  have hb_norm : ‖∏ w ∈ hfin.toFinset, -(inducedCoeff K μ w)‖ = 1 := by
    rw [norm_prod]
    exact Finset.prod_eq_one fun w hw => by rw [norm_neg, hc_norm w ((hS w).mp hw)]
  have hab : ∏ w ∈ hfin.toFinset, -(inducedCoeff K μ w)⁻¹ = (∏ w ∈ hfin.toFinset, -(inducedCoeff K μ w))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun w _ => neg_inv

  have hrefl : reflect 3 (inducedEulerPoly ℚ (inducedCoeff K μ) v) =
      ∏ w ∈ hfin.toFinset, reflect (v.asIdeal.inertiaDeg' w.asIdeal)
        (C 1 - C (inducedCoeff K μ w) * X ^ (v.asIdeal.inertiaDeg' w.asIdeal)) := by
    rw [hP, prod_reflect _ _ _ hdegQ, hsum]
  have hP'eq : inducedEulerPoly ℚ (inducedCoeff K μ⁻¹) v =
      C (∏ w ∈ hfin.toFinset, -(inducedCoeff K μ w))⁻¹ * reflect 3 (inducedEulerPoly ℚ (inducedCoeff K μ) v) := by
    rw [hP', Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, hrefl, ← hab, map_prod C]

  have hcoeff0 : (inducedEulerPoly ℚ (inducedCoeff K μ) v).coeff 0 = 1 := by
    rw [hP, coeff_zero_prod]
    exact Finset.prod_eq_one fun w hw => by
      simp [coeff_sub, coeff_C, coeff_one, coeff_X_pow, Ne.symm (hfne w hw)]
  have hcoeff3 : (inducedEulerPoly ℚ (inducedCoeff K μ) v).coeff 3 =
      ∏ w ∈ hfin.toFinset, -(inducedCoeff K μ w) := by
    have h30 : (reflect 3 (inducedEulerPoly ℚ (inducedCoeff K μ) v)).coeff 0 =
        (inducedEulerPoly ℚ (inducedCoeff K μ) v).coeff 3 := by
      rw [coeff_reflect, revAt_le (Nat.zero_le 3)]
    rw [← h30, hrefl, coeff_zero_prod]
    refine Finset.prod_congr rfl fun w hw => ?_
    rw [coeff_reflect, revAt_le (Nat.zero_le _), Nat.sub_zero]
    simp [coeff_sub, coeff_one, coeff_C_mul, coeff_X_pow, hfne w hw]

  have hbound : ∀ k, ‖(inducedEulerPoly ℚ (inducedCoeff K μ) v).coeff k‖ ≤ (Nat.choose 3 k : ℝ) := by
    intro k
    rw [hP, ← coeff_one_add_X_pow ℝ 3 k, ← hsum, ← Finset.prod_pow_eq_pow_sum]
    exact norm_coeff_prod_le _ _ _ (fun w hw k => norm_coeff_factor_le _ (hc_norm w ((hS w).mp hw)).le _
      (hfne w hw) k) k
  have hb1 := hbound 1
  have hb2 := hbound 2
  rw [show ((Nat.choose 3 1 : ℕ) : ℝ) = 3 by norm_num] at hb1
  rw [show ((Nat.choose 3 2 : ℕ) : ℝ) = 3 by rw [show Nat.choose 3 2 = 3 from rfl]; norm_num] at hb2

  unfold inducedE1 inducedE2 inducedE3
  rw [hP'eq]
  simp only [coeff_C_mul, coeff_reflect, revAt_le (show 1 ≤ 3 by norm_num), revAt_le (show 2 ≤ 3 by norm_num),
    revAt_le (show 3 ≤ 3 by norm_num), Nat.reduceSub, Nat.sub_self, hcoeff3, hcoeff0]
  set b := ∏ w ∈ hfin.toFinset, -(inducedCoeff K μ w) with hbdef
  refine ⟨neg_ne_zero.mpr hb_ne, by rw [norm_neg, hb_norm], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [inv_neg]; ring
  · rw [inv_neg]; ring
  · rw [inv_neg, mul_one]
  · rw [norm_neg, norm_mul, norm_inv, hb_norm, inv_one, one_mul]; exact hb2
  · rw [norm_mul, norm_inv, hb_norm, inv_one, one_mul]; exact hb1
  · rw [mul_one, norm_neg, norm_inv, hb_norm, inv_one]

end
end S_LanglandsTunnell_CubicInduction_inducedE_inducedCoeff_inv_eq_of_not_isBadPlace
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_inducedE_inducedCoeff_inv_eq_of_not_isBadPlace (solution)
