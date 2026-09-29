-- Prove2me | solution 1 for IsDiscreteValuationRing.index_range_powMonoidHom_units_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/4508ca06-6acf-5aa6-bb6c-4d5f4ce3cfaa

import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits
import Theorems.Thm_IsDiscreteValuationRing_exists_mem_principalUnits_pow_eq
import Theorems.Thm_IsDiscreteValuationRing_eq_one_of_pow_eq_one_of_mem_principalUnits
import Theorems.Thm_IsDiscreteValuationRing_relIndex_principalUnits_add
import Theorems.Thm_IsDiscreteValuationRing_natCard_quotient_maximalIdeal_pow
import Theorems.Thm_IsLocalRing_index_principalUnits_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_index_range_powMonoidHom_units_eq

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

namespace P2mS26G1
open IsLocalRing

theorem exists_pow_sub_one_sub_eq {R : Type*} [CommRing R] (u : R) (n : ℕ) :
    ∃ y : R, u ^ n - 1 - n * (u - 1) = (u - 1) ^ 2 * y := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨y, hy⟩ := ih
    refine ⟨u * y + n, ?_⟩
    have h : u ^ (n + 1) - 1 - ((n + 1 : ℕ) : R) * (u - 1)
        = u * (u ^ n - 1 - n * (u - 1)) + n * (u - 1) * (u - 1) := by
      push_cast; ring
    rw [h, hy]; ring

theorem pow_mem_principalUnits_add {R : Type*} [CommRing R] [IsLocalRing R] {n e k : ℕ}
    (hne : (n : R) ∈ maximalIdeal R ^ e) (hk : e ≤ k) {u : Rˣ} (hu : u ∈ principalUnits R k) :
    u ^ n ∈ principalUnits R (k + e) := by
  rw [mem_principalUnits_iff] at hu ⊢
  obtain ⟨y, hy⟩ := exists_pow_sub_one_sub_eq (u : R) n
  have h : ((u ^ n : Rˣ) : R) - 1 = n * ((u : R) - 1) + ((u : R) - 1) ^ 2 * y := by
    rw [Units.val_pow_eq_pow_val, ← hy]; ring
  rw [h]
  refine Ideal.add_mem _ ?_ (Ideal.mul_mem_right _ _ ?_)
  · rw [add_comm k e, pow_add]
    exact Ideal.mul_mem_mul hne hu
  · refine Ideal.pow_le_pow_right (show k + e ≤ k + k by omega) ?_
    rw [pow_add, sq]
    exact Ideal.mul_mem_mul hu hu

theorem exists_span_natCast_eq_maximalIdeal_pow {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {n : ℕ} (hn : (n : R) ≠ 0) :
    ∃ e : ℕ, Ideal.span {(n : R)} = maximalIdeal R ^ e := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (show Ideal.span {(n : R)} ≠ ⊥ by simpa [Ideal.span_singleton_eq_bot] using hn) hϖ
  exact ⟨e, by rw [he, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]⟩

end P2mS26G1

theorem solution {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [Finite (IsLocalRing.ResidueField R)] {n : ℕ} (hn : (n : R) ≠ 0) :
    (powMonoidHom n : Rˣ →* Rˣ).range.index
      = Nat.card (rootsOfUnity n R) * Nat.card (R ⧸ Ideal.span {(n : R)}) := by
  classical
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact hn (by simp))
  obtain ⟨e, hne⟩ := P2mS26G1.exists_span_natCast_eq_maximalIdeal_pow hn
  have hnmem : (n : R) ∈ IsLocalRing.maximalIdeal R ^ e := by
    rw [← hne]; exact Ideal.mem_span_singleton_self _
  have hk : e < e + 1 := Nat.lt_succ_self e
  have h1k : 1 ≤ e + 1 := Nat.succ_le_succ (Nat.zero_le e)

  have hmap : (IsLocalRing.principalUnits R (e + 1)).map (powMonoidHom n : Rˣ →* Rˣ) = IsLocalRing.principalUnits R (e + 1 + e) := by
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      rw [powMonoidHom_apply]
      exact P2mS26G1.pow_mem_principalUnits_add hnmem hk.le hu
    · intro w hw
      obtain ⟨u, hu, huw⟩ := IsDiscreteValuationRing.exists_mem_principalUnits_pow_eq hn0 hne hk hw
      exact ⟨u, hu, huw⟩

  have hinf : IsLocalRing.principalUnits R (e + 1) ⊓ (powMonoidHom n : Rˣ →* Rˣ).ker = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 ?_
    intro ζ hζ'
    obtain ⟨hζ, hζn⟩ := Subgroup.mem_inf.1 hζ'
    have hζn' : ζ ^ n = 1 := by rw [MonoidHom.mem_ker, powMonoidHom_apply] at hζn; exact hζn
    exact IsDiscreteValuationRing.eq_one_of_pow_eq_one_of_mem_principalUnits hne hk hζ hζn'

  have hq : 0 < Nat.card (IsLocalRing.ResidueField R) := Nat.card_pos
  have hidx1 : (IsLocalRing.principalUnits R 1).index ≠ 0 := by
    rw [IsLocalRing.index_principalUnits_one]; exact Nat.card_pos.ne'
  have hrel : (IsLocalRing.principalUnits R (e + 1)).relIndex (IsLocalRing.principalUnits R 1) = Nat.card (IsLocalRing.ResidueField R) ^ e := by
    have h := IsDiscreteValuationRing.relIndex_principalUnits_add (R := R) (k := 1) le_rfl e
    rwa [Nat.add_comm 1 e] at h
  have hidxk : (IsLocalRing.principalUnits R (e + 1)).index ≠ 0 := by
    rw [← Subgroup.relIndex_mul_index (IsLocalRing.principalUnits_antitone h1k : IsLocalRing.principalUnits R (e + 1) ≤ IsLocalRing.principalUnits R 1),
      hrel]
    exact mul_ne_zero (pow_ne_zero _ hq.ne') hidx1

  have hA : (IsLocalRing.principalUnits R (e + 1 + e)).index
      = (IsLocalRing.principalUnits R (e + 1) ⊔ (powMonoidHom n : Rˣ →* Rˣ).ker).index * (powMonoidHom n : Rˣ →* Rˣ).range.index := by
    rw [← hmap]; exact Subgroup.index_map (IsLocalRing.principalUnits R (e + 1)) (powMonoidHom n)
  have hB : (IsLocalRing.principalUnits R (e + 1 + e)).relIndex (IsLocalRing.principalUnits R (e + 1)) * (IsLocalRing.principalUnits R (e + 1)).index
      = (IsLocalRing.principalUnits R (e + 1 + e)).index :=
    Subgroup.relIndex_mul_index (IsLocalRing.principalUnits_antitone (Nat.le_add_right (e + 1) e))
  have hC : (IsLocalRing.principalUnits R (e + 1)).relIndex (IsLocalRing.principalUnits R (e + 1) ⊔ (powMonoidHom n : Rˣ →* Rˣ).ker)
        * (IsLocalRing.principalUnits R (e + 1) ⊔ (powMonoidHom n : Rˣ →* Rˣ).ker).index
      = (IsLocalRing.principalUnits R (e + 1)).index := Subgroup.relIndex_mul_index le_sup_left
  have hD : (IsLocalRing.principalUnits R (e + 1)).relIndex (IsLocalRing.principalUnits R (e + 1) ⊔ (powMonoidHom n : Rˣ →* Rˣ).ker)
      = Nat.card (powMonoidHom n : Rˣ →* Rˣ).ker := by
    rw [Subgroup.relIndex_sup_left, ← Subgroup.inf_relIndex_right, hinf, Subgroup.relIndex_bot_left]
  have hE : (IsLocalRing.principalUnits R (e + 1 + e)).relIndex (IsLocalRing.principalUnits R (e + 1)) = Nat.card (IsLocalRing.ResidueField R) ^ e :=
    IsDiscreteValuationRing.relIndex_principalUnits_add h1k e
  have hF : (powMonoidHom n : Rˣ →* Rˣ).range.index * (IsLocalRing.principalUnits R (e + 1)).index
      = (Nat.card (powMonoidHom n : Rˣ →* Rˣ).ker * Nat.card (IsLocalRing.ResidueField R) ^ e) * (IsLocalRing.principalUnits R (e + 1)).index := by
    calc (powMonoidHom n : Rˣ →* Rˣ).range.index * (IsLocalRing.principalUnits R (e + 1)).index
        = (powMonoidHom n : Rˣ →* Rˣ).range.index * (Nat.card (powMonoidHom n : Rˣ →* Rˣ).ker
            * (IsLocalRing.principalUnits R (e + 1) ⊔ (powMonoidHom n : Rˣ →* Rˣ).ker).index) := by rw [← hC, hD]
      _ = Nat.card (powMonoidHom n : Rˣ →* Rˣ).ker
            * ((IsLocalRing.principalUnits R (e + 1) ⊔ (powMonoidHom n : Rˣ →* Rˣ).ker).index
              * (powMonoidHom n : Rˣ →* Rˣ).range.index) := by ring
      _ = Nat.card (powMonoidHom n : Rˣ →* Rˣ).ker * (IsLocalRing.principalUnits R (e + 1 + e)).index := by rw [hA]
      _ = Nat.card (powMonoidHom n : Rˣ →* Rˣ).ker
            * (Nat.card (IsLocalRing.ResidueField R) ^ e * (IsLocalRing.principalUnits R (e + 1)).index) := by rw [← hB, hE]
      _ = _ := by ring
  have hG := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hidxk) hF
  have hker : (powMonoidHom n : Rˣ →* Rˣ).ker = rootsOfUnity n R := by
    ext ζ
    rw [MonoidHom.mem_ker, powMonoidHom_apply, mem_rootsOfUnity]
  rw [hG, hne, IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow, hker]

end S_IsDiscreteValuationRing_index_range_powMonoidHom_units_eq
end P2MW
export P2MW.S_IsDiscreteValuationRing_index_range_powMonoidHom_units_eq (solution)
