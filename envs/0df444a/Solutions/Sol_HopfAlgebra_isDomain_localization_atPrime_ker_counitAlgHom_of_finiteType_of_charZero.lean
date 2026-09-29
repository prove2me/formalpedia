-- Prove2me | solution 1 for HopfAlgebra.isDomain_localization_atPrime_ker_counitAlgHom_of_finiteType_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/08b102c3-b9c5-5c21-a1f8-ca1a5d06381b

import Mathlib
import Theorems.Thm_HopfAlgebra_mul_not_mem_ker_counitAlgHom_pow_succ_of_lift_basis_charZero
import Theorems.Thm_HopfAlgebra_exists_fin_lift_basis_ker_counitAlgHom_sq_of_finiteType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_isDomain_localization_atPrime_ker_counitAlgHom_of_finiteType_of_charZero

open Bialgebra

set_option maxHeartbeats 4800000

noncomputable section

theorem solution
    (K : Type*) [Field K] [CharZero K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Algebra.FiniteType K A] :
    haveI : (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom).IsPrime :=
      RingHom.ker_isPrime (Bialgebra.counitAlgHom K A).toRingHom
    IsDomain (Localization.AtPrime (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom)) := by
  haveI hIp : (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom).IsPrime :=
    RingHom.ker_isPrime (Bialgebra.counitAlgHom K A).toRingHom
  classical
  set I := RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom with hI
  set S := Localization.AtPrime I
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A

  obtain ⟨d, ξ, hξI, hξli, hξspan⟩ :=
    HopfAlgebra.exists_fin_lift_basis_ker_counitAlgHom_sq_of_finiteType K A

  have hgr : ∀ {m n : ℕ} {x y : A}, x ∈ I ^ m → x ∉ I ^ (m + 1) → y ∈ I ^ n →
      y ∉ I ^ (n + 1) → x * y ∉ I ^ (m + n + 1) := fun {m n x y} hxm hxm' hyn hyn' =>
    HopfAlgebra.mul_not_mem_ker_counitAlgHom_pow_succ_of_lift_basis_charZero
      K A hξI hξli hξspan hxm hxm' hyn hyn'

  have hsat : ∀ {x y : A}, x ∉ I → ∀ N, x * y ∈ I ^ N → y ∈ I ^ N := by
    intro x y hx N hxy
    by_contra hyn
    have hne : ∃ j, y ∉ I ^ j := ⟨N, hyn⟩
    set m₀ := Nat.find hne
    have hym₀ : y ∉ I ^ m₀ := Nat.find_spec hne
    have hm₀N : m₀ ≤ N := Nat.find_le hyn
    have hm₀pos : 1 ≤ m₀ := by
      rcases Nat.eq_zero_or_pos m₀ with h0 | hp
      · exact absurd (by rw [h0, pow_zero, Ideal.one_eq_top]; exact trivial) hym₀
      · exact hp
    have hym₀' : y ∈ I ^ (m₀ - 1) :=
      not_not.mp (Nat.find_min hne (show m₀ - 1 < m₀ by omega))
    have hx0 : x ∈ I ^ 0 := by rw [pow_zero, Ideal.one_eq_top]; exact trivial
    have hx1 : x ∉ I ^ (0 + 1) := by rwa [zero_add, pow_one]
    have hym₀'' : y ∉ I ^ (m₀ - 1 + 1) := by rwa [Nat.sub_add_cancel hm₀pos]
    have hnot : x * y ∉ I ^ (0 + (m₀ - 1) + 1) := hgr hx0 hx1 hym₀' hym₀''
    exact hnot (Ideal.pow_le_pow_right (by omega) hxy)

  have hKrullW : ∀ a : A, algebraMap A S a ≠ 0 → ∃ n, a ∉ I ^ n := by
    intro a ha
    set J := I.map (algebraMap A S) with hJ
    have hJmax : J = IsLocalRing.maximalIdeal S := by
      rw [hJ]; exact Localization.AtPrime.map_eq_maximalIdeal
    have hJne : J ≠ ⊤ := hJmax ▸ (IsLocalRing.maximalIdeal.isMaximal S).ne_top
    have hKrull : ⨅ n, J ^ n = ⊥ := J.iInf_pow_eq_bot_of_isLocalRing hJne
    have hnotbot : algebraMap A S a ∉ (⊥ : Ideal S) := by simpa [Ideal.mem_bot] using ha
    rw [← hKrull, Ideal.mem_iInf] at hnotbot
    simp only [not_forall] at hnotbot
    obtain ⟨n, hn⟩ := hnotbot
    exact ⟨n, fun han => hn (by rw [hJ, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ han)⟩

  have hNZD : ∀ z w : S, z * w = 0 → z = 0 ∨ w = 0 := by
    intro z w hzw
    by_contra hc
    rw [not_or] at hc
    obtain ⟨hz, hw⟩ := hc
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective I.primeCompl z
    obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective I.primeCompl w
    rw [← IsLocalization.mk'_mul] at hzw
    obtain ⟨u, hu⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp hzw
    have hab_all : ∀ N, a * b ∈ I ^ N := fun N =>
      hsat u.2 N (by rw [hu]; exact Ideal.zero_mem _)
    have haφ : algebraMap A S a ≠ 0 := fun h0 => hz <| by
      have hspec := IsLocalization.mk'_spec S a s
      rw [h0] at hspec
      exact (IsLocalization.map_units S s).mul_left_eq_zero.mp hspec
    have hbφ : algebraMap A S b ≠ 0 := fun h0 => hw <| by
      have hspec := IsLocalization.mk'_spec S b t
      rw [h0] at hspec
      exact (IsLocalization.map_units S t).mul_left_eq_zero.mp hspec
    obtain ⟨m, hm⟩ := hKrullW a haφ
    obtain ⟨n, hn⟩ := hKrullW b hbφ
    have hnea : ∃ j, a ∉ I ^ j := ⟨m, hm⟩
    have hneb : ∃ j, b ∉ I ^ j := ⟨n, hn⟩
    set m₀ := Nat.find hnea
    set n₀ := Nat.find hneb
    have ham₀ : a ∉ I ^ m₀ := Nat.find_spec hnea
    have hbn₀ : b ∉ I ^ n₀ := Nat.find_spec hneb
    have hm₀pos : 1 ≤ m₀ := by
      rcases Nat.eq_zero_or_pos m₀ with h0 | hp
      · exact absurd (by rw [h0, pow_zero, Ideal.one_eq_top]; exact trivial) ham₀
      · exact hp
    have hn₀pos : 1 ≤ n₀ := by
      rcases Nat.eq_zero_or_pos n₀ with h0 | hp
      · exact absurd (by rw [h0, pow_zero, Ideal.one_eq_top]; exact trivial) hbn₀
      · exact hp
    have ham₀' : a ∈ I ^ (m₀ - 1) :=
      not_not.mp (Nat.find_min hnea (show m₀ - 1 < m₀ by omega))
    have hbn₀' : b ∈ I ^ (n₀ - 1) :=
      not_not.mp (Nat.find_min hneb (show n₀ - 1 < n₀ by omega))
    have ham₀'' : a ∉ I ^ (m₀ - 1 + 1) := by rwa [Nat.sub_add_cancel hm₀pos]
    have hbn₀'' : b ∉ I ^ (n₀ - 1 + 1) := by rwa [Nat.sub_add_cancel hn₀pos]
    exact hgr ham₀' ham₀'' hbn₀' hbn₀'' (hab_all _)
  haveI : NoZeroDivisors S := ⟨fun {a b} => hNZD a b⟩
  exact { }

end

end S_HopfAlgebra_isDomain_localization_atPrime_ker_counitAlgHom_of_finiteType_of_charZero
end P2MW
export P2MW.S_HopfAlgebra_isDomain_localization_atPrime_ker_counitAlgHom_of_finiteType_of_charZero (solution)
