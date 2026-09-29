-- Prove2me | solution 1 for ModularCurve.exists_map_eq_and_isGamma0PowAt_of_isGamma0PowAt_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/c403e6b4-0651-5005-960e-53d703e204c1

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_map_eq_and_isGamma0PowAt_of_isGamma0PowAt_map

set_option autoImplicit false

universe u

open Polynomial

namespace Gamma0PowExtendsAux

theorem exists_map_eq_of_monic_of_dvd_map
    {R₀ : Type u} [CommRing R₀] [IsDomain R₀] [IsIntegrallyClosed R₀]
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    {h' : Polynomial K} (hm : h'.Monic) {f : Polynomial R₀} (hf : IsUnit f.leadingCoeff)
    (hdvd : h' ∣ f.map (algebraMap R₀ K)) :
    ∃ h₀ : Polynomial R₀, h₀.map (algebraMap R₀ K) = h' ∧ h₀.Monic := by
  obtain ⟨u, hu⟩ := hf
  have hfmonic : (C (↑u⁻¹ : R₀) * f).Monic := by
    apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [← hu, Units.inv_mul]
  have hdvd' : h' ∣ (C (↑u⁻¹ : R₀) * f).map (algebraMap R₀ K) := by
    rw [Polynomial.map_mul, Polynomial.map_C]
    exact Dvd.dvd.mul_left hdvd _
  obtain ⟨h₀, hh₀⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K hfmonic hdvd'
  rw [hm.leadingCoeff, Polynomial.C_1, mul_one] at hh₀
  refine ⟨h₀, hh₀, ?_⟩
  have hm' := hm
  rw [← hh₀] at hm'
  exact Polynomial.monic_of_injective (IsFractionRing.injective R₀ K) hm'

theorem mul_dvd_of_map_mul_dvd_map
    {R₀ S : Type u} [CommRing R₀] [CommRing S] (f : R₀ →+* S) (hf : Function.Injective f)
    {x c y : Polynomial R₀} (hx : x.Monic) (hc : IsUnit c.leadingCoeff)
    (h : (x * c).map f ∣ y.map f) : x * c ∣ y := by
  obtain ⟨u, hu⟩ := hc
  have hm : (x * c * C (↑u⁻¹ : R₀)).Monic := by
    rw [mul_assoc]
    exact hx.mul (Polynomial.monic_mul_C_of_leadingCoeff_mul_eq_one (by rw [← hu, Units.mul_inv]))
  have hunit : IsUnit (C (↑u⁻¹ : R₀)) := Polynomial.isUnit_C.mpr (Units.isUnit u⁻¹)
  rw [← hunit.mul_right_dvd, ← Polynomial.map_dvd_map f hf hm, Polynomial.map_mul, Polynomial.map_C]
  exact ((Polynomial.isUnit_C.mpr ((Units.isUnit u⁻¹).map f)).mul_right_dvd).mpr h

theorem isUnit_leadingCoeff_preΨ' {R₀ : Type u} [CommRing R₀] [Nontrivial R₀] (W₀ : WeierstrassCurve R₀)
    (n : ℕ) (hn : IsUnit ((n : ℕ) : R₀)) : IsUnit (W₀.preΨ' n).leadingCoeff := by
  have hn0 : ((n : ℕ) : R₀) ≠ 0 := hn.ne_zero
  rw [W₀.leadingCoeff_preΨ' hn0]
  split_ifs with he
  · obtain ⟨m, hm⟩ := he
    have hnm : n / 2 = m := by omega
    rw [hnm]
    have : ((n : ℕ) : R₀) = (m : R₀) * 2 := by rw [hm]; push_cast; ring
    rw [this] at hn
    exact isUnit_of_mul_isUnit_left hn
  · exact hn

theorem preΨ_pow_eq_preΨ' {R₀ : Type u} [CommRing R₀] (W₀ : WeierstrassCurve R₀) (p j : ℕ) :
    W₀.preΨ (p ^ j) = W₀.preΨ' (p ^ j) := by
  rw [← WeierstrassCurve.preΨ_ofNat]
  norm_cast

theorem map_preΨ_pow {R₀ S : Type u} [CommRing R₀] [CommRing S] (W₀ : WeierstrassCurve R₀) (f : R₀ →+* S) (p j : ℕ) :
    (W₀.map f).preΨ (p ^ j) = (W₀.preΨ' (p ^ j)).map f := by
  rw [preΨ_pow_eq_preΨ', WeierstrassCurve.map_preΨ']

end Gamma0PowExtendsAux

open Gamma0PowExtendsAux in

theorem solution
    {R₀ : Type u} [CommRing R₀] [IsDomain R₀] [IsIntegrallyClosed R₀]
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (W₀ : WeierstrassCurve R₀) (p k : ℕ) (hp : IsUnit ((p : ℕ) : R₀))
    (h' : Polynomial K) (hh' : ModularCurve.IsGamma0PowAt (W₀.map (algebraMap R₀ K)) p k h') :
    ∃ h₀ : Polynomial R₀, h₀.map (algebraMap R₀ K) = h' ∧ ModularCurve.IsGamma0PowAt W₀ p k h₀ := by
  classical
  have hinj : Function.Injective (algebraMap R₀ K) := IsFractionRing.injective R₀ K
  have hpj : ∀ j : ℕ, IsUnit ((p ^ j : ℕ) : R₀) := fun j => by rw [Nat.cast_pow]; exact hp.pow j
  by_cases hpk : p ^ k = 2
  ·
    have hh2 : (W₀.map (algebraMap R₀ K)).IsTwoKernel h' := (ModularCurve.isGamma0PowAt_of_pow_eq_two _ hpk _).1 hh'
    have h2 : IsUnit (2 : R₀) := by
      have h := hpj k
      rwa [hpk, Nat.cast_ofNat] at h
    have h4 : IsUnit (4 : R₀) := by
      have h := h2.mul h2
      norm_num at h
      exact h
    have hlc : IsUnit W₀.Ψ₂Sq.leadingCoeff := by
      rw [W₀.leadingCoeff_Ψ₂Sq h4.ne_zero]; exact h4
    have hdvd : h' ∣ W₀.Ψ₂Sq.map (algebraMap R₀ K) := by
      rw [← WeierstrassCurve.map_Ψ₂Sq]; exact hh2.dvd_Ψ₂Sq
    obtain ⟨h₀, hh₀, hmonic₀⟩ := exists_map_eq_of_monic_of_dvd_map (hh2.monic _) hlc hdvd
    have hdeg : h₀.natDegree = h'.natDegree := by
      rw [← hh₀, Polynomial.natDegree_map_eq_of_injective hinj]
    refine ⟨h₀, hh₀, (ModularCurve.isGamma0PowAt_of_pow_eq_two _ hpk _).2 ⟨?_, ?_, ?_⟩⟩
    · rw [hdeg]; exact hh2.natDegree_le
    · apply hinj
      rw [← Polynomial.coeff_map, hh₀, map_one]
      exact hh2.coeff_eq_one
    · rw [← Polynomial.map_dvd_map (algebraMap R₀ K) hinj hmonic₀, hh₀, ← WeierstrassCurve.map_Ψ₂Sq]
      exact hh2.dvd_Ψ₂Sq
  ·
    have hhg : (W₀.map (algebraMap R₀ K)).IsCyclicGenKernel p k h' :=
      (ModularCurve.isGamma0PowAt_of_pow_ne_two _ hpk _).1 hh'
    have hdvd : h' ∣ (W₀.preΨ' (p ^ k)).map (algebraMap R₀ K) := by
      rw [← map_preΨ_pow]
      exact dvd_of_mul_right_dvd hhg.mul_preΨ_dvd
    obtain ⟨h₀, hh₀, hmonic₀⟩ :=
      exists_map_eq_of_monic_of_dvd_map (hhg.monic _) (isUnit_leadingCoeff_preΨ' W₀ (p ^ k) (hpj k)) hdvd
    have hdeg : h₀.natDegree = h'.natDegree := by
      rw [← hh₀, Polynomial.natDegree_map_eq_of_injective hinj]
    refine ⟨h₀, hh₀, (ModularCurve.isGamma0PowAt_of_pow_ne_two _ hpk _).2 ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [hdeg]; exact hhg.natDegree_le
    · apply hinj
      rw [← Polynomial.coeff_map, hh₀, map_one]
      exact hhg.coeff_eq_one
    · rw [preΨ_pow_eq_preΨ', preΨ_pow_eq_preΨ']
      refine mul_dvd_of_map_mul_dvd_map (algebraMap R₀ K) hinj hmonic₀
        (isUnit_leadingCoeff_preΨ' W₀ (p ^ (k - 1)) (hpj (k - 1))) ?_
      rw [Polynomial.map_mul, hh₀, ← map_preΨ_pow, ← map_preΨ_pow]
      exact hhg.mul_preΨ_dvd
    · intro a ha ha' hpa
      rw [← Polynomial.map_dvd_map (algebraMap R₀ K) hinj hmonic₀, hh₀, ← W₀.smulNumerator_map, hh₀]
      exact hhg.dvd_smulNumerator a ha ha' hpa

end S_ModularCurve_exists_map_eq_and_isGamma0PowAt_of_isGamma0PowAt_map
end P2MW
export P2MW.S_ModularCurve_exists_map_eq_and_isGamma0PowAt_of_isGamma0PowAt_map (solution)
