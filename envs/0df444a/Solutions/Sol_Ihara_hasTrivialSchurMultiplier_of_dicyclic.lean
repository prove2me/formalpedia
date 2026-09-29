-- Prove2me | solution 1 for Ihara.hasTrivialSchurMultiplier_of_dicyclic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/bbccb6c3-dd80-5b50-9314-7b17153fe2bf

import Mathlib
import Definitions.Def_SchurMultiplierTrivial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ihara_hasTrivialSchurMultiplier_of_dicyclic

open scoped commutatorElement

theorem solution
    {G : Type*} [Group G] (x y : G) (m : ℕ)
    (hx : orderOf x = 2 * m) (hy : y ^ 2 = x ^ m) (hconj : y * x * y⁻¹ = x⁻¹)
    (hgen : Subgroup.closure {x, y} = ⊤) :
    Ihara.HasTrivialSchurMultiplier G := by
  intro E _ π hπ hcent hcomm
  classical
  obtain ⟨X, hX⟩ := hπ x
  obtain ⟨Y, hY⟩ := hπ y

  have hc : ∀ z : E, π z = 1 → ∀ g : E, g * z = z * g := fun z hz g =>
    Subgroup.mem_center_iff.mp (hcent (by rwa [MonoidHom.mem_ker])) g
  have hcC : ∀ z : E, π z = 1 → ∀ g : E, Commute z g := fun z hz g => (hc z hz g).symm

  set z₂ : E := Y * X * Y⁻¹ * X with hz₂_def
  set z₁ : E := X ^ m * (Y ^ 2)⁻¹ with hz₁_def
  have hz₂ : π z₂ = 1 := by
    simp only [hz₂_def, map_mul, map_inv, hX, hY, hconj, inv_mul_cancel]
  have hz₁ : π z₁ = 1 := by
    simp only [hz₁_def, map_mul, map_inv, map_pow, hX, hY, hy, mul_inv_cancel]
  have hc₂ : ∀ g : E, g * z₂ = z₂ * g := hc z₂ hz₂
  have hc₁ : ∀ g : E, g * z₁ = z₁ * g := hc z₁ hz₁
  have hcinv : ∀ g : E, g * z₂⁻¹ = z₂⁻¹ * g := fun g =>
    Subgroup.mem_center_iff.mp
      (inv_mem (Subgroup.mem_center_iff.mpr hc₂ : z₂ ∈ Subgroup.center E)) g

  have hYXY : Y * X * Y⁻¹ = z₂ * X⁻¹ := by
    rw [hz₂_def]; group
  have hYXinvY : Y * X⁻¹ * Y⁻¹ = X * z₂⁻¹ := by
    calc Y * X⁻¹ * Y⁻¹ = (Y * X * Y⁻¹)⁻¹ := by group
      _ = (z₂ * X⁻¹)⁻¹ := by rw [hYXY]
      _ = X * z₂⁻¹ := by group

  set v : E := z₂⁻¹ * X ^ 2 with hv_def
  have hπv : π v = x ^ 2 := by
    simp only [hv_def, map_mul, map_inv, map_pow, hz₂, hX, inv_one, one_mul]
  have hcomXY : ⁅X, Y⁆ = v := by
    calc ⁅X, Y⁆ = X * (Y * X⁻¹ * Y⁻¹) := by rw [commutatorElement_def]; group
      _ = X * (X * z₂⁻¹) := by rw [hYXinvY]
      _ = (X * X) * z₂⁻¹ := by group
      _ = z₂⁻¹ * (X * X) := hcinv (X * X)
      _ = v := by rw [hv_def, pow_two]
  have hXv : X * v * X⁻¹ = v := by
    calc X * v * X⁻¹ = (X * z₂⁻¹) * X ^ 2 * X⁻¹ := by rw [hv_def]; group
      _ = (z₂⁻¹ * X) * X ^ 2 * X⁻¹ := by rw [hcinv X]
      _ = v := by rw [hv_def]; group
  have hYv : Y * v * Y⁻¹ = v⁻¹ := by
    calc Y * v * Y⁻¹ = (Y * z₂⁻¹) * X ^ 2 * Y⁻¹ := by rw [hv_def]; group
      _ = (z₂⁻¹ * Y) * X ^ 2 * Y⁻¹ := by rw [hcinv Y]
      _ = z₂⁻¹ * ((Y * X * Y⁻¹) * (Y * X * Y⁻¹)) := by rw [pow_two]; group
      _ = z₂⁻¹ * ((z₂ * X⁻¹) * (z₂ * X⁻¹)) := by rw [hYXY]
      _ = X⁻¹ * (z₂ * X⁻¹) := by group
      _ = X⁻¹ * (X⁻¹ * z₂) := by rw [hc₂ X⁻¹]
      _ = v⁻¹ := by rw [hv_def]; group

  have hXm : z₁ * Y ^ 2 = X ^ m := by
    rw [hz₁_def]; group
  have hconjA : Y * X ^ m * Y⁻¹ = z₂ ^ m * (X⁻¹) ^ m := by
    have hcomm : Commute z₂ X⁻¹ := (hc₂ X⁻¹).symm
    rw [← hcomm.mul_pow, ← hYXY, conj_pow]
  have hconjB : Y * X ^ m * Y⁻¹ = X ^ m := by
    calc Y * X ^ m * Y⁻¹ = (Y * z₁) * Y ^ 2 * Y⁻¹ := by rw [← hXm]; group
      _ = (z₁ * Y) * Y ^ 2 * Y⁻¹ := by rw [hc₁ Y]
      _ = z₁ * Y ^ 2 := by group
      _ = X ^ m := hXm
  have hX2m : X ^ m * X ^ m = z₂ ^ m := by
    have h : X ^ m = z₂ ^ m * (X⁻¹) ^ m := hconjB.symm.trans hconjA
    calc X ^ m * X ^ m = z₂ ^ m * (X⁻¹) ^ m * X ^ m := congrArg (· * X ^ m) h
      _ = z₂ ^ m := by rw [inv_pow, inv_mul_cancel_right]
  have hvm : v ^ m = 1 := by
    have hcomm : Commute z₂⁻¹ (X ^ 2) := (hcinv (X ^ 2)).symm
    calc v ^ m = (z₂⁻¹) ^ m * (X ^ 2) ^ m := by rw [hv_def]; exact hcomm.mul_pow m
      _ = (z₂⁻¹) ^ m * (X ^ m * X ^ m) := by rw [← pow_mul, ← pow_add, two_mul]
      _ = 1 := by rw [hX2m, inv_pow, inv_mul_cancel]

  set S : Set E := {X, Y} ∪ (π.ker : Set E) with hS_def
  have hS : Subgroup.closure S = ⊤ := by
    refine eq_top_iff.mpr fun e _ => ?_
    have he : π e ∈ (Subgroup.closure {X, Y}).map π := by
      rw [MonoidHom.map_closure, Set.image_pair, hX, hY, hgen]
      exact Subgroup.mem_top _
    obtain ⟨e₀, he₀, hee₀⟩ := Subgroup.mem_map.mp he
    have h1 : e₀ ∈ Subgroup.closure S :=
      Subgroup.closure_mono Set.subset_union_left he₀
    have h2 : e₀⁻¹ * e ∈ Subgroup.closure S := by
      refine Subgroup.subset_closure (Set.subset_union_right ?_)
      rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, hee₀, inv_mul_cancel]
    have := Subgroup.mul_mem _ h1 h2
    rwa [mul_inv_cancel_left] at this

  set N : Subgroup E := Subgroup.zpowers v with hN_def
  have hvN : v ∈ N := Subgroup.mem_zpowers v
  have hgood : ∀ g : E, g * v * g⁻¹ ∈ N ∧ g⁻¹ * v * g ∈ N := by
    intro g
    have hg : g ∈ Subgroup.closure S := by rw [hS]; exact Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem s hs =>
      rcases hs with (rfl | rfl) | hs
      ·
        have h' : s⁻¹ * v * s = v := by
          calc s⁻¹ * v * s = s⁻¹ * (s * v * s⁻¹) * s := by rw [hXv]
            _ = v := by group
        rw [hXv, h']
        exact ⟨hvN, hvN⟩
      ·
        have h' : s⁻¹ * v * s = v⁻¹ := by
          have h1 : s⁻¹ * v⁻¹ * s = v := by
            calc s⁻¹ * v⁻¹ * s = s⁻¹ * (s * v * s⁻¹) * s := by rw [hYv]
              _ = v := by group
          calc s⁻¹ * v * s = (s⁻¹ * v⁻¹ * s)⁻¹ := by group
            _ = v⁻¹ := by rw [h1]
        rw [hYv, h']
        exact ⟨inv_mem hvN, inv_mem hvN⟩
      ·
        have hs' : π s = 1 := MonoidHom.mem_ker.mp hs
        have h1 : s * v * s⁻¹ = v := by rw [← hc s hs' v]; group
        have h2 : s⁻¹ * v * s = v := by rw [mul_assoc, hc s hs' v]; group
        rw [h1, h2]
        exact ⟨hvN, hvN⟩
    | one => simpa using hvN
    | mul a b _ _ iha ihb =>
      obtain ⟨ta, hta⟩ := Subgroup.mem_zpowers_iff.mp iha.2
      obtain ⟨tb, htb⟩ := Subgroup.mem_zpowers_iff.mp ihb.1
      constructor
      · have : a * b * v * (a * b)⁻¹ = (a * v * a⁻¹) ^ tb := by
          rw [conj_zpow, htb]; group
        rw [this]
        exact Subgroup.zpow_mem _ iha.1 tb
      · have : (a * b)⁻¹ * v * (a * b) = (b⁻¹ * v * b) ^ ta := by
          have h := conj_zpow (a := b⁻¹) (b := v) (i := ta)
          rw [inv_inv] at h
          rw [h, hta]; group
        rw [this]
        exact Subgroup.zpow_mem _ ihb.2 ta
    | inv a _ ih =>
      rw [inv_inv]
      exact ⟨ih.2, ih.1⟩

  haveI hN : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨t, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ (hgood g).1 t
  let φ : E →* E ⧸ N := QuotientGroup.mk' N
  have hφXY : Commute (φ X) (φ Y) := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement, hcomXY]
    exact (QuotientGroup.eq_one_iff v).mpr hvN
  have hSS : ∀ s ∈ S, ∀ t ∈ S, Commute (φ s) (φ t) := by
    intro s hs t ht
    rcases hs with (rfl | rfl) | hs
    · rcases ht with (rfl | rfl) | ht
      · exact Commute.refl _
      · exact hφXY
      · exact ((hcC t (MonoidHom.mem_ker.mp ht) s).map φ).symm
    · rcases ht with (rfl | rfl) | ht
      · exact hφXY.symm
      · exact Commute.refl _
      · exact ((hcC t (MonoidHom.mem_ker.mp ht) s).map φ).symm
    · exact (hcC s (MonoidHom.mem_ker.mp hs) t).map φ
  have hS1 : ∀ s ∈ S, ∀ b : E, Commute (φ s) (φ b) := by
    intro s hs b
    have hb : b ∈ Subgroup.closure S := by rw [hS]; exact Subgroup.mem_top b
    induction hb using Subgroup.closure_induction with
    | mem t ht => exact hSS s hs t ht
    | one => rw [map_one]; exact Commute.one_right _
    | mul a b _ _ iha ihb => rw [map_mul]; exact iha.mul_right ihb
    | inv a _ ih => rw [map_inv]; exact ih.inv_right
  have hS2 : ∀ a b : E, Commute (φ a) (φ b) := by
    intro a b
    have ha : a ∈ Subgroup.closure S := by rw [hS]; exact Subgroup.mem_top a
    induction ha using Subgroup.closure_induction with
    | mem s hs => exact hS1 s hs b
    | one => rw [map_one]; exact Commute.one_left _
    | mul a a' _ _ iha iha' => rw [map_mul]; exact iha.mul_left iha'
    | inv a _ ih => rw [map_inv]; exact ih.inv_left
  have hcommN : commutator E ≤ N := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro g ⟨a, b, rfl⟩
    refine (QuotientGroup.eq_one_iff _).mp ?_
    rw [← QuotientGroup.mk'_apply, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact hS2 a b

  refine (Subgroup.eq_bot_iff_forall _).mpr fun a ha => ?_
  obtain ⟨t, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hcommN (hcomm ha))
  have hπa : x ^ ((2 : ℤ) * t) = 1 := by
    have h := MonoidHom.mem_ker.mp ha
    rwa [map_zpow, hπv, ← zpow_natCast, ← zpow_mul, Nat.cast_ofNat] at h
  have hdvd : ((2 * m : ℕ) : ℤ) ∣ 2 * t := by
    rw [← hx]; exact orderOf_dvd_iff_zpow_eq_one.mpr hπa
  have hmt : (m : ℤ) ∣ t := by
    rw [Nat.cast_mul, Nat.cast_ofNat] at hdvd
    exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp hdvd
  obtain ⟨s, rfl⟩ := hmt
  rw [zpow_mul, zpow_natCast, hvm, one_zpow]

end S_Ihara_hasTrivialSchurMultiplier_of_dicyclic
end P2MW
export P2MW.S_Ihara_hasTrivialSchurMultiplier_of_dicyclic (solution)
