-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.inducedE_inv_eq_of_finrank_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/2aa289a0-0d8c-534c-9d06-edebe86801e5

import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_inducedE_inv_eq_of_finrank_eq_three

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction
open Polynomial

noncomputable section

namespace Ws23IE

theorem ringHom_ratInt_ext {T : Type*} [NonAssocSemiring T] (f g : 𝓞 ℚ →+* T) : f = g := by
  have h : f.comp Rat.ringOfIntegersEquiv.symm.toRingHom = g.comp Rat.ringOfIntegersEquiv.symm.toRingHom :=
    RingHom.ext_int _ _
  ext x
  have h2 := RingHom.congr_fun h (Rat.ringOfIntegersEquiv x)
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply] at h2
  exact h2

section Cubic

variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)]

@[reducible] def algOK : Algebra (𝓞 ℚ) K := ((algebraMap (𝓞 K) K).comp (algebraMap (𝓞 ℚ) (𝓞 K))).toAlgebra

theorem sum_ramification_inertia_eq_finrank (p : HeightOneSpectrum (𝓞 ℚ)) :
    ∑ P ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 K),
      Ideal.ramificationIdx' p.asIdeal P * Ideal.inertiaDeg' p.asIdeal P = Module.finrank ℚ K := by
  letI : Algebra (𝓞 ℚ) K := algOK K
  haveI : IsScalarTower (𝓞 ℚ) (𝓞 K) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (𝓞 ℚ) ℚ K := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    have h := ringHom_ratInt_ext ((algebraMap ℚ K).comp (algebraMap (𝓞 ℚ) ℚ)) (algebraMap (𝓞 ℚ) K)
    exact (congrArg (fun φ : 𝓞 ℚ →+* K => φ x) h).symm
  haveI : Module.Finite (𝓞 ℚ) (𝓞 K) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 ℚ) (𝓞 K)
  haveI := p.isMaximal
  exact Ideal.sum_ramification_inertia (R := 𝓞 ℚ) (S := 𝓞 K) (K := ℚ) (L := K) p.ne_bot

end Cubic

section PolyDual

variable {ι : Type*}

theorem reflect_factor (a : ℂ) (n : ℕ) :
    reflect n (C 1 - C a * X ^ n : ℂ[X]) = X ^ n - C a := by
  rw [reflect_sub, reflect_C, reflect_C_mul_X_pow, revAt_le (le_refl n), Nat.sub_self, pow_zero, mul_one, map_one,
    one_mul]

theorem factor_inv_eq (a : ℂ) (ha : a ≠ 0) (n : ℕ) :
    (C 1 - C a⁻¹ * X ^ n : ℂ[X]) = C (-a⁻¹) * (X ^ n - C a) := by
  have h : C (-a⁻¹) * C a = (-1 : ℂ[X]) := by
    rw [← C_mul, neg_mul, inv_mul_cancel₀ ha, map_neg, map_one]
  rw [mul_sub, h, map_neg, map_one]
  ring_nf

theorem natDegree_factor_le (a : ℂ) (n : ℕ) : (C 1 - C a * X ^ n : ℂ[X]).natDegree ≤ n := by
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · rw [map_one, natDegree_one]; exact Nat.zero_le _
  · exact (natDegree_C_mul_X_pow_le a n)

theorem prod_factor_inv_eq_C_mul_reflect (T : Finset ι) (a : ι → ℂ) (n : ι → ℕ) (ha : ∀ i ∈ T, a i ≠ 0)
    (hn : ∀ i ∈ T, 1 ≤ n i) :
    (∏ i ∈ T, (C 1 - C (a i)⁻¹ * X ^ (n i) : ℂ[X])) =
      C (∏ i ∈ T, (-(a i))⁻¹) * reflect (∑ i ∈ T, n i) (∏ i ∈ T, (C 1 - C (a i) * X ^ (n i) : ℂ[X])) ∧
    (∏ i ∈ T, (C 1 - C (a i) * X ^ (n i) : ℂ[X])).natDegree ≤ ∑ i ∈ T, n i ∧
    (reflect (∑ i ∈ T, n i) (∏ i ∈ T, (C 1 - C (a i) * X ^ (n i) : ℂ[X]))).coeff 0 = ∏ i ∈ T, (-(a i)) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨?_, ?_, ?_⟩
    · simp [reflect_one]
    · simp
    · simp [reflect_one]
  | insert j T hj ih =>
    obtain ⟨h1, h2, h3⟩ := ih (fun i hi => ha i (Finset.mem_insert_of_mem hi)) (fun i hi => hn i (Finset.mem_insert_of_mem hi))
    have haj : a j ≠ 0 := ha j (Finset.mem_insert_self _ _)
    have hnj : ¬ (0 = n j) := by have := hn j (Finset.mem_insert_self _ _); omega
    have hrefl : reflect (∑ i ∈ insert j T, n i) (∏ i ∈ insert j T, (C 1 - C (a i) * X ^ (n i) : ℂ[X])) =
        (X ^ (n j) - C (a j)) * reflect (∑ i ∈ T, n i) (∏ i ∈ T, (C 1 - C (a i) * X ^ (n i) : ℂ[X])) := by
      rw [Finset.sum_insert hj, Finset.prod_insert hj, reflect_mul _ _ (natDegree_factor_le (a j) (n j)) h2,
        reflect_factor]
    refine ⟨?_, ?_, ?_⟩
    · rw [Finset.prod_insert hj, Finset.prod_insert hj, h1, hrefl, factor_inv_eq (a j) haj, map_mul]
      ring
    · rw [Finset.prod_insert hj, Finset.sum_insert hj]
      exact (natDegree_mul_le).trans (Nat.add_le_add (natDegree_factor_le _ _) h2)
    · rw [hrefl, Finset.prod_insert hj, coeff_zero_eq_eval_zero, eval_mul, ← coeff_zero_eq_eval_zero,
        ← coeff_zero_eq_eval_zero, h3]
      simp [hnj]

theorem coeff_zero_prod_factor (T : Finset ι) (a : ι → ℂ) (n : ι → ℕ) (hn : ∀ i ∈ T, 1 ≤ n i) :
    (∏ i ∈ T, (C 1 - C (a i) * X ^ (n i) : ℂ[X])).coeff 0 = 1 := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert j T hj ih =>
    rw [Finset.prod_insert hj, coeff_zero_eq_eval_zero, eval_mul, ← coeff_zero_eq_eval_zero,
      ← coeff_zero_eq_eval_zero, ih (fun i hi => hn i (Finset.mem_insert_of_mem hi))]
    have h1 : 1 ≤ n j := hn j (Finset.mem_insert_self _ _)
    simp [coeff_X_pow, Nat.pos_iff_ne_zero.1 h1 |>.symm]

end PolyDual

section Fibre

variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

theorem algebraMap_OO_injective : Function.Injective (algebraMap (𝓞 ℚ) (𝓞 K)) := by
  have h := ringHom_ratInt_ext (algebraMap (𝓞 ℚ) (𝓞 K))
    ((algebraMap ℤ (𝓞 K)).comp Rat.ringOfIntegersEquiv.toRingHom)
  rw [h]
  exact (algebraMap ℤ (𝓞 K)).injective_int.comp Rat.ringOfIntegersEquiv.injective

theorem isTorsionFree_OO : Module.IsTorsionFree (𝓞 ℚ) (𝓞 K) :=
  (Module.isTorsionFree_iff_algebraMap_injective).2 (algebraMap_OO_injective K)

theorem mem_primeFibre_iff (p : HeightOneSpectrum (𝓞 ℚ)) (𝔓 : HeightOneSpectrum (𝓞 K)) :
    𝔓 ∈ primeFibre ℚ K p ↔ 𝔓.asIdeal ∈ p.asIdeal.primesOver (𝓞 K) := by
  rw [mem_primeFibre]
  constructor
  · intro h
    refine ⟨𝔓.isPrime, (Ideal.liesOver_iff _ _).2 ?_⟩
    rw [← h, HeightOneSpectrum.under_asIdeal]
  · rintro ⟨-, hover⟩
    apply HeightOneSpectrum.ext
    rw [HeightOneSpectrum.under_asIdeal, ← (Ideal.liesOver_iff _ _).1 hover]

theorem primeFibre_finite (p : HeightOneSpectrum (𝓞 ℚ)) : (primeFibre ℚ K p).Finite := by
  haveI := p.isMaximal
  haveI := isTorsionFree_OO K
  have h : primeFibre ℚ K p = (fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.asIdeal) ⁻¹' p.asIdeal.primesOver (𝓞 K) := by
    ext 𝔓; exact mem_primeFibre_iff K p 𝔓
  rw [h]
  exact (IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 K)).preimage
    fun _ _ _ _ h => HeightOneSpectrum.ext h

theorem sum_primesOverFinset_eq_sum_fibre (p : HeightOneSpectrum (𝓞 ℚ)) (f : Ideal (𝓞 K) → ℕ) :
    ∑ P ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 K), f P =
      ∑ 𝔓 ∈ (primeFibre_finite K p).toFinset, f 𝔓.asIdeal := by
  classical
  haveI := p.isMaximal
  haveI := isTorsionFree_OO K
  symm
  refine Finset.sum_bij (fun 𝔓 _ => 𝔓.asIdeal) (fun 𝔓 h𝔓 => ?_) (fun _ _ _ _ h => HeightOneSpectrum.ext h)
    (fun P hP => ?_) (fun _ _ => rfl)
  · rw [IsDedekindDomain.mem_primesOverFinset_iff p.ne_bot]
    exact (mem_primeFibre_iff K p 𝔓).1 ((primeFibre_finite K p).mem_toFinset.1 h𝔓)
  · rw [IsDedekindDomain.mem_primesOverFinset_iff p.ne_bot] at hP
    refine ⟨⟨P, hP.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot hP⟩, ?_, rfl⟩
    exact (primeFibre_finite K p).mem_toFinset.2 ((mem_primeFibre_iff K p _).2 hP)

theorem sum_inertiaDeg_eq_three (hdeg : Module.finrank ℚ K = 3) (p : HeightOneSpectrum (𝓞 ℚ)) (hp : ¬ IsRamifiedIn K p) :
    ∑ 𝔓 ∈ (primeFibre_finite K p).toFinset, Ideal.inertiaDeg' p.asIdeal 𝔓.asIdeal = 3 := by
  have hsum := sum_ramification_inertia_eq_finrank K p
  rw [hdeg, sum_primesOverFinset_eq_sum_fibre K p] at hsum
  rw [← hsum]
  refine Finset.sum_congr rfl fun 𝔓 h𝔓 => ?_
  have hmem := (primeFibre_finite K p).mem_toFinset.1 h𝔓
  have he : Ideal.ramificationIdx' p.asIdeal 𝔓.asIdeal = 1 := by
    by_contra hne
    exact hp ⟨𝔓, hmem, hne⟩
  rw [he, one_mul]

theorem one_le_inertiaDeg (p : HeightOneSpectrum (𝓞 ℚ)) (𝔓 : HeightOneSpectrum (𝓞 K)) (h𝔓 : 𝔓 ∈ primeFibre ℚ K p) :
    1 ≤ Ideal.inertiaDeg' p.asIdeal 𝔓.asIdeal := by
  haveI := p.isMaximal
  haveI : Module.Finite (𝓞 ℚ) (𝓞 K) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 ℚ) (𝓞 K)
  haveI : 𝔓.asIdeal.LiesOver p.asIdeal := ((mem_primeFibre_iff K p 𝔓).1 h𝔓).2
  exact Ideal.inertiaDeg'_pos p.asIdeal 𝔓.asIdeal

theorem inducedEulerPoly_eq_prod (p : HeightOneSpectrum (𝓞 ℚ)) (c : HeightOneSpectrum (𝓞 K) → ℂ) :
    inducedEulerPoly ℚ c p =
      ∏ 𝔓 ∈ (primeFibre_finite K p).toFinset, (C 1 - C (c 𝔓) * X ^ (Ideal.inertiaDeg' p.asIdeal 𝔓.asIdeal)) := by
  unfold inducedEulerPoly
  rw [finprod_mem_eq_finite_toFinset_prod _ (primeFibre_finite K p)]
  refine Finset.prod_congr rfl fun 𝔓 h𝔓 => ?_
  have hmem : 𝔓.under (𝓞 ℚ) = p := (primeFibre_finite K p).mem_toFinset.1 h𝔓
  unfold inducedFactor
  rw [hmem]

end Fibre

theorem inducedE_inv (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3) (c : HeightOneSpectrum (𝓞 K) → ℂ) (p : HeightOneSpectrum (𝓞 ℚ))
    (hp : ¬ IsRamifiedIn K p) (hc : ∀ 𝔓 ∈ primeFibre ℚ K p, c 𝔓 ≠ 0) :
    inducedE3 ℚ c p ≠ 0 ∧
      inducedE1 ℚ (fun 𝔓 => (c 𝔓)⁻¹) p = inducedE2 ℚ c p * (inducedE3 ℚ c p)⁻¹ ∧
      inducedE2 ℚ (fun 𝔓 => (c 𝔓)⁻¹) p = inducedE1 ℚ c p * (inducedE3 ℚ c p)⁻¹ ∧
      inducedE3 ℚ (fun 𝔓 => (c 𝔓)⁻¹) p = (inducedE3 ℚ c p)⁻¹ := by
  classical
  set T := (primeFibre_finite K p).toFinset with hT
  set n : HeightOneSpectrum (𝓞 K) → ℕ := fun 𝔓 => Ideal.inertiaDeg' p.asIdeal 𝔓.asIdeal with hn
  have hcT : ∀ 𝔓 ∈ T, c 𝔓 ≠ 0 := fun 𝔓 h => hc 𝔓 ((primeFibre_finite K p).mem_toFinset.1 h)
  have hnT : ∀ 𝔓 ∈ T, 1 ≤ n 𝔓 := fun 𝔓 h => one_le_inertiaDeg K p 𝔓 ((primeFibre_finite K p).mem_toFinset.1 h)
  have hsum : ∑ 𝔓 ∈ T, n 𝔓 = 3 := sum_inertiaDeg_eq_three K hdeg p hp

  have hP : inducedEulerPoly ℚ c p = ∏ 𝔓 ∈ T, (C 1 - C (c 𝔓) * X ^ (n 𝔓)) := inducedEulerPoly_eq_prod K p c
  have hQ : inducedEulerPoly ℚ (fun 𝔓 => (c 𝔓)⁻¹) p = ∏ 𝔓 ∈ T, (C 1 - C (c 𝔓)⁻¹ * X ^ (n 𝔓)) :=
    inducedEulerPoly_eq_prod K p _
  obtain ⟨hQP, -, hlead⟩ := prod_factor_inv_eq_C_mul_reflect T c n hcT hnT
  rw [hsum] at hQP hlead
  set P := ∏ 𝔓 ∈ T, (C 1 - C (c 𝔓) * X ^ (n 𝔓)) with hPdef
  set L := ∏ 𝔓 ∈ T, (-(c 𝔓)) with hLdef
  have hL : L ≠ 0 := Finset.prod_ne_zero_iff.2 fun 𝔓 h => neg_ne_zero.2 (hcT 𝔓 h)
  have hu : (∏ 𝔓 ∈ T, (-(c 𝔓))⁻¹) = L⁻¹ := by rw [hLdef, Finset.prod_inv_distrib]
  have hP3 : P.coeff 3 = L := by rw [← hlead, coeff_reflect, revAt_zero]
  have hP0 : P.coeff 0 = 1 := coeff_zero_prod_factor T c n hnT

  have hQk : ∀ k : ℕ, k ≤ 3 → (inducedEulerPoly ℚ (fun 𝔓 => (c 𝔓)⁻¹) p).coeff k = L⁻¹ * P.coeff (3 - k) := by
    intro k hk
    rw [hQ, hQP, hu, coeff_C_mul, coeff_reflect, revAt_le hk]

  have hE1 : inducedE1 ℚ c p = -P.coeff 1 := by unfold inducedE1; rw [hP]
  have hE2 : inducedE2 ℚ c p = P.coeff 2 := by unfold inducedE2; rw [hP]
  have hE3 : inducedE3 ℚ c p = -L := by unfold inducedE3; rw [hP, hP3]
  have hE1' : inducedE1 ℚ (fun 𝔓 => (c 𝔓)⁻¹) p = -(L⁻¹ * P.coeff 2) := by unfold inducedE1; rw [hQk 1 (by norm_num)]
  have hE2' : inducedE2 ℚ (fun 𝔓 => (c 𝔓)⁻¹) p = L⁻¹ * P.coeff 1 := by unfold inducedE2; rw [hQk 2 (by norm_num)]
  have hE3' : inducedE3 ℚ (fun 𝔓 => (c 𝔓)⁻¹) p = -(L⁻¹ * P.coeff 0) := by unfold inducedE3; rw [hQk 3 (by norm_num)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hE3]; exact neg_ne_zero.2 hL
  · rw [hE1', hE2, hE3, inv_neg]; ring
  · rw [hE2', hE1, hE3, inv_neg]; ring
  · rw [hE3', hE3, hP0, inv_neg]; ring

end Ws23IE

theorem solution
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3) (c : HeightOneSpectrum (𝓞 K) → ℂ) (p : HeightOneSpectrum (𝓞 ℚ))
    (hp : ¬ IsRamifiedIn K p) (hc : ∀ 𝔓 ∈ primeFibre ℚ K p, c 𝔓 ≠ 0) :
    inducedE3 ℚ c p ≠ 0 ∧
      inducedE1 ℚ (fun 𝔓 => (c 𝔓)⁻¹) p = inducedE2 ℚ c p * (inducedE3 ℚ c p)⁻¹ ∧
      inducedE2 ℚ (fun 𝔓 => (c 𝔓)⁻¹) p = inducedE1 ℚ c p * (inducedE3 ℚ c p)⁻¹ ∧
      inducedE3 ℚ (fun 𝔓 => (c 𝔓)⁻¹) p = (inducedE3 ℚ c p)⁻¹ :=
  Ws23IE.inducedE_inv K hdeg c p hp hc

end

#print axioms solution

end S_LanglandsTunnell_RankinSelberg_inducedE_inv_eq_of_finrank_eq_three
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_inducedE_inv_eq_of_finrank_eq_three (solution)
