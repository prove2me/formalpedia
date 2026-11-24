-- Prove2me | solution 1 for GlobalTheory.SimMult.exists_norm_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:16:04.998342+00:00
-- url     : https://prove2.me/submissions/920538c8-c6a1-4e75-bfa0-1a72da30f3d7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSimTrivialOfMult
import Theorems.Thm_GlobalTheory_SimMult_lift_pow
import Theorems.Thm_GlobalTheory_SimMult_norm_congr
import Theorems.Thm_GlobalTheory_SimMult_mem_sup_mul
import Theorems.Thm_GlobalTheory_SimMult_mem_of_mul_eq_span
import Theorems.Thm_GlobalTheory_SimMult_mem_sup_of_coprime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SimMult
variable {O : Type*} [CommRing O] (σ : O →+* O)
namespace GlobalTheory.SimMult
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) {w : O} (hw : w + σ w = 1) (ν : ℤ)
    (hnorm : ∀ n : ℕ, 0 < n → IsCoprime ν (n : ℤ) → ∃ c, (n : O) ∣ c * σ c - ν)
    (M A : ℕ) (J : Ideal O) (hprod : J * J.map σ = Ideal.span {(M : O)}) (hcop : J ⊔ J.map σ = ⊤)
    (hA : (A : ℤ) ∣ ν - 1) (n : ℕ) :
    0 < n → IsCoprime ν (n : ℤ) → ∃ c, (n : O) ∣ c * σ c - ν ∧ c - 1 ∈ J ⊔ Ideal.span {(n : O)} ∧
      c - 1 ∈ Ideal.span {(A : O)} ⊔ Ideal.span {(n : O)} := by
  have hMJ : (M : O) ∈ J := mem_of_mul_eq_span hprod
  have hA' : (A : O) ∣ ν - 1 := by
    have := map_dvd (Int.castRingHom O) hA
    simpa using this
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; omega
  | one => intro _ _; exact ⟨1, by simp, by simp, by simp⟩
  | prime_pow r k hr hk =>
    intro hn hν
    by_cases hM : r ∣ M
    · have h1 : IsCoprime (J ^ k) (J.map σ ^ k) := (Ideal.isCoprime_iff_sup_eq.2 hcop).pow
      obtain ⟨e', he', e, he, hee⟩ := Ideal.isCoprime_iff_exists.1 h1
      have hσe' : σ e' ∈ J.map σ ^ k := by
        rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem σ he'
      have hσe : σ e ∈ J ^ k := by
        have h2 := Ideal.mem_map_of_mem σ he
        have h3 : σ.comp σ = RingHom.id O := RingHom.ext hσ
        rwa [Ideal.map_pow, Ideal.map_map, h3, Ideal.map_id] at h2
      have hσee := congrArg σ hee
      rw [map_add, map_one] at hσee
      have hc1 : e + ν * e' - 1 = (ν - 1) * e' := by linear_combination hee
      refine ⟨e + ν * e', ?_, ?_, ?_⟩
      · have h4 : (e + ν * e') * σ (e + ν * e') - ν ∈ J ^ k * J.map σ ^ k := by
          have : (e + ν * e') * σ (e + ν * e') - ν
              = (1 - ν) * (σ e * e) + (ν * ν - ν) * (e' * σ e') := by
            rw [map_add, map_mul, map_intCast]
            linear_combination (ν * (σ e' + σ e)) * hee + ν * hσee
          rw [this]
          exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hσe he))
            (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul he' hσe'))
        rw [← mul_pow, hprod, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h4
        refine dvd_trans ?_ h4
        rw [Nat.cast_pow]
        exact pow_dvd_pow_of_dvd (Nat.cast_dvd_cast hM) k
      · rw [hc1]
        exact Ideal.mem_sup_left (J.mul_mem_left _ (Ideal.pow_le_self hk.ne' he'))
      · rw [hc1]
        exact Ideal.mem_sup_left (Ideal.mem_span_singleton.2 (hA'.mul_right _))
    have hMc : Nat.Coprime M (r ^ k) := ((Nat.Prime.coprime_iff_not_dvd hr).2 hM).symm.pow_right k
    by_cases hrA : r ∣ A
    · obtain ⟨c, h1, h2⟩ := lift_pow σ hσ hw (Ideal.span {(A : O)}) ν 1
        (by simpa [Ideal.mem_span_singleton] using hA') 1
        (by rw [Ideal.mem_span_singleton, map_one, one_mul]; exact dvd_sub_comm.1 hA') k
      refine ⟨c, ?_, mem_sup_of_coprime J hMJ hMc _, Ideal.mem_sup_left h1⟩
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h2
      refine dvd_trans ?_ h2
      rw [Nat.cast_pow]
      exact pow_dvd_pow_of_dvd (Nat.cast_dvd_cast hrA) k
    · have hAc : Nat.Coprime A (r ^ k) :=
        ((Nat.Prime.coprime_iff_not_dvd hr).2 hrA).symm.pow_right k
      obtain ⟨c, hc⟩ := hnorm _ hn hν
      exact ⟨c, hc, mem_sup_of_coprime J hMJ hMc _,
        mem_sup_of_coprime _ (Ideal.mem_span_singleton_self _) hAc _⟩
  | coprime a b ha hb hab iha ihb =>
    intro _ hν
    rw [Nat.cast_mul] at hν
    obtain ⟨c₁, h1, h2, h3⟩ := iha (by omega) hν.of_mul_right_left
    obtain ⟨c₂, h4, h5, h6⟩ := ihb (by omega) hν.of_mul_right_right
    have hco := Nat.Coprime.cast (R := O) hab
    obtain ⟨u, v, huv⟩ := hco
    have e1 : c₁ + (c₂ - c₁) * u * a - c₁ = (c₂ - c₁) * u * a := by ring
    have e2 : c₁ + (c₂ - c₁) * u * a - c₂ = (c₁ - c₂) * v * b := by
      linear_combination (c₂ - c₁) * huv
    have side : ∀ K : Ideal O, c₁ - 1 ∈ K ⊔ Ideal.span {(a : O)} →
        c₂ - 1 ∈ K ⊔ Ideal.span {(b : O)} →
        c₁ + (c₂ - c₁) * u * a - 1 ∈ K ⊔ Ideal.span {((a * b : ℕ) : O)} := by
      intro K k1 k2
      rw [Nat.cast_mul]
      refine mem_sup_mul K huv ?_ ?_
      · have := Ideal.add_mem _ k1 (Ideal.mem_sup_right (S := K)
          (Ideal.mem_span_singleton'.2 ⟨_, e1.symm⟩))
        convert this using 1; ring
      · have := Ideal.add_mem _ k2 (Ideal.mem_sup_right (S := K)
          (Ideal.mem_span_singleton'.2 ⟨_, e2.symm⟩))
        convert this using 1; ring
    refine ⟨c₁ + (c₂ - c₁) * u * a, ?_, side _ h2 h5, side _ h3 h6⟩
    rw [Nat.cast_mul]
    refine IsCoprime.mul_dvd ⟨u, v, huv⟩ ?_ ?_
    · rw [← Ideal.mem_span_singleton] at h1 ⊢
      refine norm_congr σ _ (Ideal.mem_span_singleton'.2 ⟨_, e1.symm⟩) ?_ h1
      rw [e1, map_mul, map_natCast]
      exact Ideal.mem_span_singleton'.2 ⟨_, rfl⟩
    · rw [← Ideal.mem_span_singleton] at h4 ⊢
      refine norm_congr σ _ (Ideal.mem_span_singleton'.2 ⟨_, e2.symm⟩) ?_ h4
      rw [e2, map_mul, map_natCast]
      exact Ideal.mem_span_singleton'.2 ⟨_, rfl⟩
end GlobalTheory.SimMult
