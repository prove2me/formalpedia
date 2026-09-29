-- Prove2me | solution 1 for IsDiscreteValuationRing.exists_primesOver_integralClosure_eq_singleton_of_forall_dvd_ramificationIdx
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/d5bd494d-dc59-51b3-9bf1-c1a8814b65a9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_exists_primesOver_integralClosure_eq_singleton_of_forall_dvd_ramificationIdx

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (F : Type*) [Field F] [Algebra O F] [IsFractionRing O F]
    (E : Type*) [Field E] [Algebra F E] [Algebra O E] [IsScalarTower O F E]
    [FiniteDimensional F E]
    [IsDedekindDomain ↥(integralClosure O E)] [Module.Finite O ↥(integralClosure O E)]
    [IsFractionRing ↥(integralClosure O E) E]
    (n : ℕ) (hn : Module.finrank F E ≤ n)
    (hdvd : ∀ (𝔓 : Ideal ↥(integralClosure O E)) [𝔓.IsPrime], 𝔓 ≠ ⊥ →
      𝔓.LiesOver (IsLocalRing.maximalIdeal O) → n ∣ (IsLocalRing.maximalIdeal O).ramificationIdx' 𝔓) :
    ∃ (𝔓 : Ideal ↥(integralClosure O E)), 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      (IsLocalRing.maximalIdeal O).primesOver ↥(integralClosure O E) = {𝔓} ∧
      (IsLocalRing.maximalIdeal O).ramificationIdx' 𝔓 = n ∧
      (IsLocalRing.maximalIdeal O).inertiaDeg' 𝔓 = 1 ∧
      Module.finrank F E = n := by
  classical
  set p := IsLocalRing.maximalIdeal O with hpdef
  have hp0 : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field O

  have hinjE : Function.Injective (algebraMap O E) := by
    rw [IsScalarTower.algebraMap_eq O F E]
    exact (algebraMap F E).injective.comp (IsFractionRing.injective O F)
  have hinjR : Function.Injective (algebraMap O ↥(integralClosure O E)) := fun x y hxy =>
    hinjE (by rw [IsScalarTower.algebraMap_apply O ↥(integralClosure O E) E x, IsScalarTower.algebraMap_apply O ↥(integralClosure O E) E y, hxy])
  haveI : FaithfulSMul O ↥(integralClosure O E) := (faithfulSMul_iff_algebraMap_injective O ↥(integralClosure O E)).mpr hinjR
  haveI : Module.IsTorsionFree O ↥(integralClosure O E) := Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance
  have hmap0 : Ideal.map (algebraMap O ↥(integralClosure O E)) p ≠ ⊥ := by
    intro h
    apply hp0
    rw [eq_bot_iff]
    intro x hx
    have : algebraMap O ↥(integralClosure O E) x = 0 := by
      rw [← Ideal.mem_bot, ← h]
      exact Ideal.mem_map_of_mem _ hx
    exact (map_eq_zero_iff _ hinjR).mp this

  have hsum := Ideal.sum_ramification_inertia (R := O) ↥(integralClosure O E) F E hp0

  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := ↥(integralClosure O E)) p
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinjR]; exact bot_le)
  haveI hQp : Q.IsPrime := hQmax.isPrime
  haveI hQover : Q.LiesOver p := ⟨hQ.symm⟩
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply hp0
    rw [← hQ, Ideal.comap_bot_of_injective _ hinjR]
  have hQmem : Q ∈ IsDedekindDomain.primesOverFinset p ↥(integralClosure O E) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 ↥(integralClosure O E)).mpr ⟨hQp, hQover⟩

  have hfr : 0 < Module.finrank F E := Module.finrank_pos
  have hn0 : 0 < n := lt_of_lt_of_le hfr hn
  have hterm : ∀ P ∈ IsDedekindDomain.primesOverFinset p ↥(integralClosure O E), n ≤ p.ramificationIdx' P * p.inertiaDeg' P := by
    intro P hP
    obtain ⟨hPp, hPover⟩ := (IsDedekindDomain.mem_primesOverFinset_iff hp0 ↥(integralClosure O E)).mp hP
    have he0 : p.ramificationIdx' P ≠ 0 :=
      Ideal.IsDedekindDomain.ramificationIdx_ne_zero hmap0 hPp (Ideal.map_le_of_le_comap (le_of_eq hPover.over))
    have hf0 : 0 < p.inertiaDeg' P := Ideal.inertiaDeg'_pos p P
    have hP0 : P ≠ ⊥ := by
      rintro rfl
      exact he0 (Ideal.ramificationIdx_bot' hp0 hinjR)
    have hdvdP : n ∣ p.ramificationIdx' P := hdvd P hP0 hPover
    calc n ≤ p.ramificationIdx' P := Nat.le_of_dvd (Nat.pos_of_ne_zero he0) hdvdP
      _ ≤ p.ramificationIdx' P * p.inertiaDeg' P := Nat.le_mul_of_pos_right _ hf0

  have hcard : (IsDedekindDomain.primesOverFinset p ↥(integralClosure O E)).card = 1 := by
    have h1 : (IsDedekindDomain.primesOverFinset p ↥(integralClosure O E)).card * n ≤ n := by
      calc (IsDedekindDomain.primesOverFinset p ↥(integralClosure O E)).card * n
          = (IsDedekindDomain.primesOverFinset p ↥(integralClosure O E)).card • n := (smul_eq_mul _ _).symm
        _ ≤ ∑ P ∈ IsDedekindDomain.primesOverFinset p ↥(integralClosure O E), p.ramificationIdx' P * p.inertiaDeg' P :=
          Finset.card_nsmul_le_sum _ _ _ hterm
        _ = Module.finrank F E := hsum
        _ ≤ n := hn
    have h2 : 0 < (IsDedekindDomain.primesOverFinset p ↥(integralClosure O E)).card := Finset.card_pos.mpr ⟨Q, hQmem⟩
    have h3 : (IsDedekindDomain.primesOverFinset p ↥(integralClosure O E)).card ≤ 1 := by
      by_contra h
      push Not at h
      have : 2 * n ≤ (IsDedekindDomain.primesOverFinset p ↥(integralClosure O E)).card * n := Nat.mul_le_mul_right n h
      omega
    omega
  obtain ⟨P₀, hP₀⟩ := Finset.card_eq_one.mp hcard
  have hQP₀ : Q = P₀ := by
    have := hQmem
    rw [hP₀, Finset.mem_singleton] at this
    exact this
  subst hQP₀

  rw [hP₀, Finset.sum_singleton] at hsum
  have hdvdQ : n ∣ p.ramificationIdx' Q := hdvd Q hQ0 hQover
  have he_ge : n ≤ p.ramificationIdx' Q :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero fun h => by rw [h, zero_mul] at hsum; omega) hdvdQ
  have hf1 : p.inertiaDeg' Q = 1 := by
    have hfpos : 0 < p.inertiaDeg' Q := Ideal.inertiaDeg'_pos p Q
    by_contra hf
    have hf2 : 2 ≤ p.inertiaDeg' Q := by omega
    have : p.ramificationIdx' Q * 2 ≤ p.ramificationIdx' Q * p.inertiaDeg' Q := Nat.mul_le_mul_left _ hf2
    omega
  rw [hf1, mul_one] at hsum
  refine ⟨Q, hQp, hQ0, ?_, by omega, hf1, by omega⟩
  rw [← IsDedekindDomain.coe_primesOverFinset hp0 ↥(integralClosure O E), hP₀, Finset.coe_singleton]

end S_IsDiscreteValuationRing_exists_primesOver_integralClosure_eq_singleton_of_forall_dvd_ramificationIdx
end P2MW
export P2MW.S_IsDiscreteValuationRing_exists_primesOver_integralClosure_eq_singleton_of_forall_dvd_ramificationIdx (solution)
