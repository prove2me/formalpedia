-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.inducedE3_eq_neg_one_pow_mul_finprod_of_not_isRamifiedIn_of_finrank_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/b9746464-065e-568b-adad-16e8cde4caa0

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_inducedE3_eq_neg_one_pow_mul_finprod_of_not_isRamifiedIn_of_finrank_eq_three

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg Polynomial

namespace P2mInducedE3

theorem natDegree_le_and_coeff_prod_one_sub_C_mul_X_pow {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (c : ι → ℂ) (f : ι → ℕ) (hf : ∀ i ∈ s, 1 ≤ f i) :
    (∏ i ∈ s, (C 1 - C (c i) * X ^ (f i))).natDegree ≤ ∑ i ∈ s, f i ∧
      (∏ i ∈ s, (C 1 - C (c i) * X ^ (f i))).coeff (∑ i ∈ s, f i) = ∏ i ∈ s, (-c i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hf' : ∀ i ∈ s, 1 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    obtain ⟨hdeg, hcoeff⟩ := ih hf'
    have hfa : 1 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hdega : (C 1 - C (c a) * X ^ (f a)).natDegree ≤ f a := by
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · simp
      · exact natDegree_C_mul_X_pow_le (c a) (f a)
    have hcoeffa : (C 1 - C (c a) * X ^ (f a)).coeff (f a) = -c a := by
      rw [coeff_sub, coeff_C, if_neg (by omega), coeff_C_mul_X_pow, if_pos rfl, zero_sub]
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    refine ⟨(natDegree_mul_le).trans (Nat.add_le_add hdega hdeg), ?_⟩
    rw [coeff_mul_add_eq_of_natDegree_le hdega hdeg, hcoeffa, hcoeff]

end P2mInducedE3

open P2mInducedE3 in
theorem solution
    (K : Type) [Field K] [NumberField K] (hdeg : Module.finrank ℚ K = 3)
    (c : HeightOneSpectrum (𝓞 K) → ℂ) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ IsRamifiedIn K v) :
    inducedE3 ℚ c v = (-1) ^ (Nat.card (primeFibre ℚ K v) + 1) * ∏ᶠ w ∈ primeFibre ℚ K v, c w := by
  classical
  have hv0 : v.asIdeal ≠ ⊥ := v.ne_bot
  haveI : v.asIdeal.IsMaximal := v.isMaximal

  have hmem : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∈ primeFibre ℚ K v ↔ 𝔓.asIdeal.LiesOver v.asIdeal := by
    intro 𝔓
    rw [mem_primeFibre, Ideal.liesOver_iff]
    constructor
    · rintro rfl
      rfl
    · intro h
      exact HeightOneSpectrum.ext h.symm

  have hfin : (primeFibre ℚ K v).Finite := by
    have hpre : primeFibre ℚ K v = (fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.asIdeal) ⁻¹'
        (v.asIdeal.primesOver (𝓞 K)) := by
      ext 𝔓
      rw [hmem, Set.mem_preimage]
      exact ⟨fun h => ⟨𝔓.isPrime, h⟩, fun h => h.2⟩
    rw [hpre]
    exact (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 K)).preimage
      (fun _ _ _ _ h => HeightOneSpectrum.ext h)
  set s : Finset (HeightOneSpectrum (𝓞 K)) := hfin.toFinset with hsdef
  have hs : (↑s : Set (HeightOneSpectrum (𝓞 K))) = primeFibre ℚ K v := hfin.coe_toFinset
  have hms : ∀ 𝔓, 𝔓 ∈ s ↔ 𝔓 ∈ primeFibre ℚ K v := fun 𝔓 => hfin.mem_toFinset

  set f : HeightOneSpectrum (𝓞 K) → ℕ := fun 𝔓 => v.asIdeal.inertiaDeg' 𝔓.asIdeal with hfdef
  have hfpos : ∀ 𝔓 ∈ s, 1 ≤ f 𝔓 := by
    intro 𝔓 h𝔓
    haveI : 𝔓.asIdeal.LiesOver v.asIdeal := (hmem 𝔓).mp ((hms 𝔓).mp h𝔓)
    exact Ideal.inertiaDeg'_pos v.asIdeal 𝔓.asIdeal

  have he : ∀ 𝔓 ∈ s, Ideal.ramificationIdx' v.asIdeal 𝔓.asIdeal = 1 := by
    intro 𝔓 h𝔓
    by_contra hne
    exact hv ⟨𝔓, (hms 𝔓).mp h𝔓, hne⟩

  have hsum : ∑ 𝔓 ∈ s, f 𝔓 = 3 := by
    have key := Ideal.sum_ramification_inertia (R := 𝓞 ℚ) (𝓞 K) ℚ K (p := v.asIdeal) hv0
    rw [hdeg] at key
    rw [← key]
    refine Finset.sum_nbij (fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.asIdeal) ?_ ?_ ?_ ?_
    · intro 𝔓 h𝔓
      have hl : 𝔓.asIdeal.LiesOver v.asIdeal := (hmem 𝔓).mp ((hms 𝔓).mp h𝔓)
      exact (IsDedekindDomain.mem_primesOverFinset_iff hv0 (𝓞 K)).mpr ⟨𝔓.isPrime, hl⟩
    · intro 𝔓 _ 𝔓' _ h
      exact HeightOneSpectrum.ext h
    · intro P hP
      rw [Finset.mem_coe] at hP
      have hP' := (IsDedekindDomain.mem_primesOverFinset_iff hv0 (𝓞 K)).mp hP
      have hPne : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hv0 hP'
      refine ⟨⟨P, hP'.1, hPne⟩, ?_, rfl⟩
      rw [Finset.mem_coe, hms, hmem]
      exact hP'.2
    · intro 𝔓 h𝔓
      rw [he 𝔓 h𝔓, one_mul]

  have hpoly : inducedEulerPoly ℚ c v = ∏ 𝔓 ∈ s, (C 1 - C (c 𝔓) * X ^ (f 𝔓)) := by
    rw [inducedEulerPoly, ← hs, finprod_mem_coe_finset]
    refine Finset.prod_congr rfl fun 𝔓 h𝔓 => ?_
    have hu : 𝔓.under (𝓞 ℚ) = v := (mem_primeFibre ℚ v 𝔓).mp ((hms 𝔓).mp h𝔓)
    simp only [inducedFactor, hu, hfdef]
  obtain ⟨-, hcoeff⟩ := natDegree_le_and_coeff_prod_one_sub_C_mul_X_pow s c f hfpos
  rw [hsum] at hcoeff
  have hcard : Nat.card (primeFibre ℚ K v) = s.card := by
    rw [← hs, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [inducedE3, hpoly, hcoeff, Finset.prod_neg, hcard, ← hs, finprod_mem_coe_finset, pow_succ]
  ring

end S_LanglandsTunnell_RankinSelberg_inducedE3_eq_neg_one_pow_mul_finprod_of_not_isRamifiedIn_of_finrank_eq_three
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_inducedE3_eq_neg_one_pow_mul_finprod_of_not_isRamifiedIn_of_finrank_eq_three (solution)
