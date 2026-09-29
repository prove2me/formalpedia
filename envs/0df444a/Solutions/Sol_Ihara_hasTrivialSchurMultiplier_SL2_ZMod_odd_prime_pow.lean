-- Prove2me | solution 1 for Ihara.hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/0ada5bd7-7687-569a-857e-bfdbd2c872cf

import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Module
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Definitions.Def_SchurMultiplierTrivial
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.ZMod.QuotientGroup
import Theorems.Thm_Ihara_exists_pow_prime_pow_eq_one_of_sl2_stem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow

section Inl_P2B_TransferSubgroup

namespace Ihara
p2m_export "Ihara" "HasTrivialSchurMultiplier hasTrivialSchurMultiplier_of_subsingleton exists_pow_prime_pow_eq_one_of_sl2_stem"
p2m_open "Ihara"

open Subgroup

open scoped commutatorElement

variable {E G : Type*} [Group E] [Group G]

theorem pow_index_mem_ker_inf_commutator_comap (π : E →* G) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ center E) (H : Subgroup G) [H.FiniteIndex]
    {x : E} (hx : x ∈ π.ker) (hxcomm : x ∈ commutator E) :
    x ^ H.index ∈ π.ker ⊓ ⁅H.comap π, H.comap π⁆ := by
  classical
  set H' := H.comap π with hH'
  have hidx : H'.index = H.index := H.index_comap_of_surjective hπ
  haveI : H'.FiniteIndex := ⟨by rw [hidx]; exact FiniteIndex.index_ne_zero⟩
  refine ⟨pow_mem hx _, ?_⟩

  let ϕ : ↥H' →* Abelianization ↥H' := Abelianization.of
  have hkey : ∀ (k : ℕ) (g₀ : E), g₀⁻¹ * x ^ k * g₀ ∈ H' → g₀⁻¹ * x ^ k * g₀ = x ^ k := by
    intro k g₀ _
    have hxc : x ^ k ∈ center E := pow_mem (hcen hx) k
    rw [mul_assoc, ← mem_center_iff.mp hxc g₀, inv_mul_cancel_left]
  have htr := MonoidHom.transfer_eq_pow ϕ x hkey

  have hker : MonoidHom.transfer ϕ x = 1 :=
    MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker (MonoidHom.transfer ϕ) hxcomm)
  rw [htr] at hker
  have hmem : (⟨x ^ H'.index, MonoidHom.transfer_eq_pow_aux x hkey⟩ : ↥H') ∈ commutator ↥H' := by
    rw [← Abelianization.ker_of]
    exact MonoidHom.mem_ker.mpr hker

  have hmap : (commutator ↥H').map H'.subtype = ⁅H', H'⁆ := by
    rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, H'.range_subtype]
  rw [← hidx, ← hmap]
  exact ⟨_, hmem, rfl⟩

theorem commutator_comap_eq_bot_of_isCyclic (π : E →* G) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ center E) (H : Subgroup G) [IsCyclic H] :
    ⁅H.comap π, H.comap π⁆ = ⊥ := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := ↥H)
  obtain ⟨c, hc⟩ := hπ γ

  have hsplit : ∀ u ∈ H.comap π, ∃ (k : ℤ) (z : E), z ∈ π.ker ∧ u = c ^ k * z := by
    intro u hu
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hγ ⟨π u, hu⟩)
    have hk' : (γ : G) ^ k = π u := by rw [← coe_zpow, hk]
    refine ⟨k, (c ^ k)⁻¹ * u, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hc, hk', inv_mul_cancel]
  rw [eq_bot_iff, commutator_le]
  intro u hu v hv
  obtain ⟨k, z, hz, rfl⟩ := hsplit u hu
  obtain ⟨l, w, hw, rfl⟩ := hsplit v hv
  have hzc := mem_center_iff.mp (hcen hz)
  have hwc := mem_center_iff.mp (hcen hw)
  rw [mem_bot, commutatorElement_eq_one_iff_commute]
  show c ^ k * z * (c ^ l * w) = c ^ l * w * (c ^ k * z)
  calc c ^ k * z * (c ^ l * w)
      = c ^ k * (z * c ^ l) * w := by group
    _ = c ^ k * (c ^ l * z) * w := by rw [← hzc (c ^ l)]
    _ = c ^ (k + l) * (z * w) := by rw [zpow_add]; group
    _ = c ^ (l + k) * (w * z) := by rw [add_comm k l, hwc z]
    _ = c ^ l * (c ^ k * w) * z := by rw [zpow_add]; group
    _ = c ^ l * (w * c ^ k) * z := by rw [hwc (c ^ k)]
    _ = c ^ l * w * (c ^ k * z) := by group

theorem pow_index_eq_one_of_isCyclic_of_stem (π : E →* G) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ center E) (H : Subgroup G) [H.FiniteIndex] [IsCyclic H]
    {x : E} (hx : x ∈ π.ker) (hxcomm : x ∈ commutator E) : x ^ H.index = 1 := by
  have h := pow_index_mem_ker_inf_commutator_comap π hπ hcen H hx hxcomm
  rw [commutator_comap_eq_bot_of_isCyclic π hπ hcen H, inf_bot_eq, mem_bot] at h
  exact h

section LocalTriviality

universe u v

variable {E : Type u} {G : Type v} [Group E] [Group G]

theorem ker_inf_commutator_comap_eq_bot_of_local (π : E →* G) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ center E) (H : Subgroup G)
    (hH : ∀ (E' : Type u) [Group E'] (π' : E' →* ↥H), Function.Surjective π' →
      π'.ker ≤ center E' → π'.ker ⊓ commutator E' = ⊥) :
    π.ker ⊓ ⁅H.comap π, H.comap π⁆ = ⊥ := by
  set H' := H.comap π with hH'
  let π' : ↥H' →* ↥H := π.subgroupComap H
  have hsurj' : Function.Surjective π' := π.subgroupComap_surjective_of_surjective H hπ
  have hker' : ∀ y : ↥H', y ∈ π'.ker ↔ (y : E) ∈ π.ker := fun y => by
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, Subtype.ext_iff]
    rfl
  have hcen' : π'.ker ≤ center ↥H' := fun y hy => by
    rw [mem_center_iff]
    intro z
    apply Subtype.ext
    change (z : E) * y = y * z
    exact mem_center_iff.mp (hcen ((hker' y).mp hy)) z
  have h := hH (↥H') π' hsurj' hcen'
  have hmap : (commutator ↥H').map H'.subtype = ⁅H', H'⁆ := by
    rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, H'.range_subtype]
  rw [eq_bot_iff]
  rintro x ⟨hx, hxc⟩
  rw [← hmap] at hxc
  obtain ⟨y, hy, rfl⟩ := hxc
  have hy' : y ∈ π'.ker ⊓ commutator ↥H' := ⟨(hker' y).mpr hx, hy⟩
  rw [h, mem_bot] at hy'
  rw [mem_bot, hy']
  rfl

theorem pow_index_eq_one_of_local (π : E →* G) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ center E) (H : Subgroup G) [H.FiniteIndex]
    (hH : ∀ (E' : Type u) [Group E'] (π' : E' →* ↥H), Function.Surjective π' →
      π'.ker ≤ center E' → π'.ker ⊓ commutator E' = ⊥)
    {x : E} (hx : x ∈ π.ker) (hxcomm : x ∈ commutator E) : x ^ H.index = 1 := by
  have h := pow_index_mem_ker_inf_commutator_comap π hπ hcen H hx hxcomm
  rw [ker_inf_commutator_comap_eq_bot_of_local π hπ hcen H hH, mem_bot] at h
  exact h

end LocalTriviality

end Ihara

end Inl_P2B_TransferSubgroup

section Inl_P2B_M2Fibre

set_option autoImplicit false

namespace Ihara
p2m_export "Ihara" "HasTrivialSchurMultiplier hasTrivialSchurMultiplier_of_subsingleton exists_pow_prime_pow_eq_one_of_sl2_stem"
p2m_open "Ihara"

open Subgroup

section CommMap

variable {E : Type*} [Group E]

def commMap (M : Subgroup E) [M.Normal] (hM : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x) (t : E) :
    M →* E where
  toFun w := t * w * t⁻¹ * (w : E)⁻¹
  map_one' := by simp
  map_mul' w w' := by
    have h2 : t * (w' : E) * t⁻¹ * (w' : E)⁻¹ ∈ M :=
      M.mul_mem (Normal.conj_mem inferInstance _ w'.2 t) (M.inv_mem w'.2)
    have key : t * (w' : E) * t⁻¹ * (w' : E)⁻¹ * (w : E)⁻¹
        = (w : E)⁻¹ * (t * (w' : E) * t⁻¹ * (w' : E)⁻¹) :=
      hM _ h2 _ (M.inv_mem w.2)
    calc t * ((w * w' : M) : E) * t⁻¹ * ((w * w' : M) : E)⁻¹
        = t * (w : E) * t⁻¹ * (t * (w' : E) * t⁻¹ * (w' : E)⁻¹ * (w : E)⁻¹) := by
          rw [Subgroup.coe_mul]; group
      _ = t * (w : E) * t⁻¹ * (w : E)⁻¹ * (t * (w' : E) * t⁻¹ * (w' : E)⁻¹) := by
          rw [key]; group

variable (M : Subgroup E) [M.Normal] (hM : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x) (t : E)

theorem commMap_apply (w : M) : commMap M hM t w = t * w * t⁻¹ * (w : E)⁻¹ := rfl

theorem commMap_mem (w : M) : commMap M hM t w ∈ M :=
  M.mul_mem (Normal.conj_mem inferInstance _ w.2 t) (M.inv_mem w.2)

theorem conj_mem_range_commMap {n : E} (hn : n ∈ (commMap M hM t).range) :
    t * n * t⁻¹ ∈ (commMap M hM t).range := by
  obtain ⟨w, rfl⟩ := hn
  refine ⟨⟨t * w * t⁻¹, Normal.conj_mem inferInstance _ w.2 t⟩, ?_⟩
  simp only [commMap_apply]
  group

theorem conj_inv_mem_range_commMap {n : E} (hn : n ∈ (commMap M hM t).range) :
    t⁻¹ * n * t ∈ (commMap M hM t).range := by
  obtain ⟨w, rfl⟩ := hn
  have hw : t⁻¹ * w * t⁻¹⁻¹ ∈ M := Normal.conj_mem inferInstance _ w.2 t⁻¹
  refine ⟨⟨t⁻¹ * w * t, by simpa using hw⟩, ?_⟩
  simp only [commMap_apply]
  group

theorem zpow_conj_mem_range_commMap (i : ℤ) {n : E} (hn : n ∈ (commMap M hM t).range) :
    t ^ i * n * t ^ (-i) ∈ (commMap M hM t).range := by
  induction i using Int.induction_on generalizing n with
  | zero => simpa using hn
  | succ i ih =>
    have h := conj_mem_range_commMap M hM t (ih hn)
    have e : t * (t ^ (i : ℤ) * n * t ^ (-(i : ℤ))) * t⁻¹
        = t ^ ((i : ℤ) + 1) * n * t ^ (-((i : ℤ) + 1)) := by group
    rwa [e] at h
  | pred i ih =>
    have h := conj_inv_mem_range_commMap M hM t (ih hn)
    have e : t⁻¹ * (t ^ (-(i : ℤ)) * n * t ^ (-(-(i : ℤ)))) * t
        = t ^ (-(i : ℤ) - 1) * n * t ^ (-(-(i : ℤ) - 1)) := by group
    rwa [e] at h

theorem zpow_comm_mem_range_commMap (i : ℤ) {w : E} (hw : w ∈ M) :
    t ^ i * w * t ^ (-i) * w⁻¹ ∈ (commMap M hM t).range := by
  induction i using Int.induction_on with
  | zero => simp
  | succ i ih =>

    have h1 : t ^ (i : ℤ) * (t * w * t⁻¹ * w⁻¹) * t ^ (-(i : ℤ)) ∈ (commMap M hM t).range :=
      zpow_conj_mem_range_commMap M hM t i ⟨⟨w, hw⟩, rfl⟩
    have e : t ^ ((i : ℤ) + 1) * w * t ^ (-((i : ℤ) + 1)) * w⁻¹
        = t ^ (i : ℤ) * (t * w * t⁻¹ * w⁻¹) * t ^ (-(i : ℤ))
          * (t ^ (i : ℤ) * w * t ^ (-(i : ℤ)) * w⁻¹) := by
      group
    rw [e]
    exact mul_mem h1 ih
  | pred i ih =>

    have h0 : t⁻¹ * (t * w * t⁻¹ * w⁻¹)⁻¹ * t ∈ (commMap M hM t).range :=
      conj_inv_mem_range_commMap M hM t (inv_mem ⟨⟨w, hw⟩, rfl⟩)
    have h1 := zpow_conj_mem_range_commMap M hM t (-(i : ℤ)) h0
    have e : t ^ (-(i : ℤ) - 1) * w * t ^ (-(-(i : ℤ) - 1)) * w⁻¹
        = t ^ (-(i : ℤ)) * (t⁻¹ * (t * w * t⁻¹ * w⁻¹)⁻¹ * t) * t ^ (-(-(i : ℤ)))
          * (t ^ (-(i : ℤ)) * w * t ^ (-(-(i : ℤ))) * w⁻¹) := by
      group
    rw [e]
    exact mul_mem h1 ih

theorem comm_zpow_mul_mem_range_commMap (i j : ℤ) {w₁ w₂ : E} (hw₁ : w₁ ∈ M)
    (hw₂ : w₂ ∈ M) :
    (t ^ i * w₁) * (t ^ j * w₂) * (t ^ i * w₁)⁻¹ * (t ^ j * w₂)⁻¹
      ∈ (commMap M hM t).range := by

  have hcomm : w₁ * w₂ * w₁⁻¹ * w₂⁻¹ = 1 := by
    rw [hM w₁ hw₁ w₂ hw₂]; group
  have p1 : w₁ * (t ^ j * w₂) * w₁⁻¹ * (t ^ j * w₂)⁻¹
      ∈ (commMap M hM t).range := by

    have e : w₁ * (t ^ j * w₂) * w₁⁻¹ * (t ^ j * w₂)⁻¹
        = (t ^ j * w₁ * t ^ (-j) * w₁⁻¹)⁻¹
          * (t ^ j * (w₁ * w₂ * w₁⁻¹ * w₂⁻¹) * t ^ (-j)) := by
      group
    rw [e, hcomm, mul_one, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
    exact inv_mem (zpow_comm_mem_range_commMap M hM t j hw₁)

  have p2 : t ^ i * (t ^ j * w₂) * t ^ (-i) * (t ^ j * w₂)⁻¹
      ∈ (commMap M hM t).range := by
    have e : t ^ i * (t ^ j * w₂) * t ^ (-i) * (t ^ j * w₂)⁻¹
        = t ^ j * (t ^ i * w₂ * t ^ (-i) * w₂⁻¹) * t ^ (-j) := by group
    rw [e]
    exact zpow_conj_mem_range_commMap M hM t j
      (zpow_comm_mem_range_commMap M hM t i hw₂)

  have e : (t ^ i * w₁) * (t ^ j * w₂) * (t ^ i * w₁)⁻¹ * (t ^ j * w₂)⁻¹
      = t ^ i * (w₁ * (t ^ j * w₂) * w₁⁻¹ * (t ^ j * w₂)⁻¹) * t ^ (-i)
        * (t ^ i * (t ^ j * w₂) * t ^ (-i) * (t ^ j * w₂)⁻¹) := by
    group
  rw [e]
  exact mul_mem (zpow_conj_mem_range_commMap M hM t i p1) p2

end CommMap

section Fibre

variable {E G Q : Type*} [Group E] [Group G] [Group Q]

theorem ker_eq_bot_of_stem_of_fibre (π : E →* G) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ center E) (hC : π.ker ≤ commutator E)
    (K : Subgroup G) [K.Normal]
    (hWab : ∀ x ∈ K.comap π, ∀ y ∈ K.comap π, x * y = y * x)
    {q : ℕ} (hCq : ∀ c ∈ π.ker, c ^ q = 1)
    (ρ : G →* Q) (hK : ρ.ker = K) (u : G)
    [((zpowers (ρ u)).comap ρ).FiniteIndex]
    (hidx : Nat.Coprime ((zpowers (ρ u)).comap ρ).index q)
    (hcent : ∀ k ∈ K, u * k = k * u → k ∈ zpowers u) :
    π.ker = ⊥ := by
  set H : Subgroup G := (zpowers (ρ u)).comap ρ with hH
  haveI : (K.comap π).Normal := Subgroup.normal_comap _
  obtain ⟨ũ, hũ⟩ := hπ u
  refine (Subgroup.eq_bot_iff_forall _).mpr fun c hc => ?_

  have h1 := pow_index_mem_ker_inf_commutator_comap π hπ hcen H hc (hC hc)
  have hcH : c ∈ ⁅H.comap π, H.comap π⁆ := by
    have hbz : (1 : ℤ) = (H.index : ℤ) * H.index.gcdA q + (q : ℤ) * H.index.gcdB q := by
      have h := Nat.gcd_eq_gcd_ab H.index q
      rw [Nat.Coprime.gcd_eq_one hidx] at h
      exact_mod_cast h
    have e : c = (c ^ H.index) ^ H.index.gcdA q * (c ^ q) ^ H.index.gcdB q := by
      conv_lhs => rw [← zpow_one c, hbz]
      rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
    rw [hCq c hc, one_zpow, mul_one] at e
    rw [e]
    exact Subgroup.zpow_mem _ h1.2 _

  have hdec : ∀ a ∈ H.comap π, ∃ i : ℤ, ∃ w ∈ K.comap π, a = ũ ^ i * w := by
    intro a ha
    rw [mem_comap, hH, mem_comap, mem_zpowers_iff] at ha
    obtain ⟨i, hi⟩ := ha
    refine ⟨i, ũ ^ (-i) * a, ?_, by group⟩
    rw [mem_comap, ← hK, MonoidHom.mem_ker, map_mul, map_zpow, hũ, map_mul, map_zpow,
      ← hi]
    group
  have hle : ⁅H.comap π, H.comap π⁆ ≤ (commMap (K.comap π) hWab ũ).range := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨i, w₁, hw₁, rfl⟩ := hdec a ha
    obtain ⟨j, w₂, hw₂, rfl⟩ := hdec b hb
    exact comm_zpow_mul_mem_range_commMap (K.comap π) hWab ũ i j hw₁ hw₂

  obtain ⟨w, hw⟩ := hle hcH
  rw [commMap_apply] at hw
  have hk : u * π w = π w * u := by
    have h := congrArg π hw
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hũ, (MonoidHom.mem_ker).mp hc] at h
    calc u * π w = u * π w * u⁻¹ * (π w)⁻¹ * (π w * u) := by group
      _ = π w * u := by rw [h, one_mul]
  have hwK : π (w : E) ∈ K := w.2
  obtain ⟨a, ha⟩ := mem_zpowers_iff.mp (hcent _ hwK hk)
  set c' : E := ũ ^ (-a) * w with hc'
  have hc'ker : c' ∈ π.ker := by
    rw [MonoidHom.mem_ker, hc', map_mul, map_zpow, hũ, ← ha]
    group
  have hcc : ∀ g : E, g * c' = c' * g := mem_center_iff.mp (hcen hc'ker)
  have hw' : (w : E) = ũ ^ a * c' := by rw [hc']; group
  rw [← hw, hw']
  calc ũ * (ũ ^ a * c') * ũ⁻¹ * (ũ ^ a * c')⁻¹
      = ũ * ũ ^ a * (c' * ũ⁻¹ * c'⁻¹) * (ũ ^ a)⁻¹ := by group
    _ = ũ * ũ ^ a * ũ⁻¹ * (ũ ^ a)⁻¹ := by rw [← hcc ũ⁻¹, mul_inv_cancel_right]
    _ = 1 := by group

end Fibre

end Ihara

end Inl_P2B_M2Fibre

section Inl_A3_CongruenceQuotientKill

namespace Ihara
p2m_export "Ihara" "HasTrivialSchurMultiplier hasTrivialSchurMultiplier_of_subsingleton exists_pow_prime_pow_eq_one_of_sl2_stem"
p2m_open "Ihara"

open Matrix

open scoped MatrixGroups

section Torsion

variable {A : Type*} [AddCommGroup A]

theorem eq_zero_of_two_nsmul (h2 : ∀ a : A, a + a = 0 → a = 0) {a : A} (h : 2 • a = 0) : a = 0 :=
  h2 a (by rwa [two_nsmul] at h)

theorem eq_zero_of_three_nsmul (h3 : ∀ a : A, a + a + a = 0 → a = 0) {a : A} (h : 3 • a = 0) :
    a = 0 :=
  h3 a (by rwa [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, two_nsmul, one_nsmul] at h)

theorem eq_zero_of_twentyfour_nsmul (h2 : ∀ a : A, a + a = 0 → a = 0)
    (h3 : ∀ a : A, a + a + a = 0 → a = 0) {a : A} (h : 24 • a = 0) : a = 0 := by
  have h12 : 12 • a = 0 :=
    eq_zero_of_two_nsmul h2 (by rwa [← mul_nsmul, show (2 * 12 : ℕ) = 24 from rfl])
  have h6 : 6 • a = 0 :=
    eq_zero_of_two_nsmul h2 (by rwa [← mul_nsmul, show (2 * 6 : ℕ) = 12 from rfl])
  have h3' : 3 • a = 0 :=
    eq_zero_of_two_nsmul h2 (by rwa [← mul_nsmul, show (2 * 3 : ℕ) = 6 from rfl])
  exact eq_zero_of_three_nsmul h3 h3'

end Torsion

section TorusTrick

theorem exists_coprime_gcd_sq_sub_one_dvd (M : ℕ) (hM : M ≠ 0) :
    ∃ t : ℕ, 1 ≤ t ∧ t.Coprime M ∧ (t ^ 2 - 1).gcd M ∣ 24 := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hM
  have hco : (2 ^ k).Coprime m := (Nat.coprime_two_left.mpr hm).pow_left k
  obtain ⟨t₀, ht₀2, ht₀m⟩ := Nat.chineseRemainder hco 3 2

  set t := t₀ + 3 * (2 ^ k * m) with ht
  have ht3 : 3 ≤ t := by
    have : 1 ≤ 2 ^ k * m := Nat.one_le_iff_ne_zero.mpr hM
    omega
  have ht2 : t ≡ 3 [MOD 2 ^ k] :=
    (Nat.ModEq.add_right _ ht₀2).trans (by
      rw [Nat.ModEq, Nat.add_mod, Nat.mul_mod, Nat.mul_mod_right, mul_zero, Nat.zero_mod, add_zero,
        Nat.mod_mod])
  have htm : t ≡ 2 [MOD m] :=
    (Nat.ModEq.add_right _ ht₀m).trans (by
      rw [Nat.ModEq, Nat.add_mod, Nat.mul_mod, mul_comm (2 ^ k) m, Nat.mul_mod_right, mul_zero,
        Nat.zero_mod, add_zero, Nat.mod_mod])
  refine ⟨t, by omega, ?_, ?_⟩
  ·
    refine Nat.Coprime.mul_right ?_ ?_
    ·
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · apply Nat.Coprime.pow_right
        rw [Nat.coprime_two_right]
        have h2 : t ≡ 3 [MOD 2] := Nat.ModEq.of_dvd (dvd_pow_self 2 hk.ne') ht2
        rw [Nat.odd_iff, h2]
    · have := htm.gcd_eq
      rw [Nat.Coprime, this]
      exact Nat.Coprime.coprime_dvd_left (by norm_num : 2 ∣ 2) (Nat.coprime_two_left.mpr hm)
  ·
    rw [Nat.Coprime.gcd_mul _ hco, show (24 : ℕ) = 8 * 3 from rfl]
    refine Nat.mul_dvd_mul ?_ ?_
    · have h9 : t ^ 2 ≡ 9 [MOD 2 ^ k] := ht2.pow 2
      have h8 : t ^ 2 - 1 ≡ 8 [MOD 2 ^ k] :=
        Nat.ModEq.add_right_cancel' 1 (by rwa [Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))])
      rw [h8.gcd_eq]
      exact Nat.gcd_dvd_left 8 _
    · have h4 : t ^ 2 ≡ 4 [MOD m] := htm.pow 2
      have h3 : t ^ 2 - 1 ≡ 3 [MOD m] :=
        Nat.ModEq.add_right_cancel' 1 (by rwa [Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))])
      rw [h3.gcd_eq]
      exact Nat.gcd_dvd_left 3 _

variable {A : Type*} [AddCommGroup A]

theorem addMonoidHom_zmod_eq_zero_of_units {M : ℕ} [NeZero M] (h2 : ∀ a : A, a + a = 0 → a = 0)
    (h3 : ∀ a : A, a + a + a = 0 → a = 0) (f : ZMod M →+ A)
    (hf : ∀ (t : (ZMod M)ˣ) (b : ZMod M), f (((t : ZMod M) ^ 2 - 1) * b) = 0) : f = 0 := by
  obtain ⟨t, ht1, htco, hgcd⟩ := exists_coprime_gcd_sq_sub_one_dvd M (NeZero.ne M)
  set g := (t ^ 2 - 1).gcd M with hg

  have hbez : ((g : ℕ) : ZMod M) =
      (((t ^ 2 - 1 : ℕ) : ℤ) : ZMod M) * ((Nat.gcdA (t ^ 2 - 1) M : ℤ) : ZMod M) := by
    have h := congrArg (fun z : ℤ => (z : ZMod M)) (Nat.gcd_eq_gcd_ab (t ^ 2 - 1) M)
    simp only [Int.cast_natCast, Int.cast_add, Int.cast_mul, ZMod.natCast_self, zero_mul,
      add_zero] at h
    rw [hg, h, Int.cast_natCast]
  have hunit : (((t ^ 2 - 1 : ℕ) : ℤ) : ZMod M) = ((ZMod.unitOfCoprime t htco : (ZMod M)ˣ) : ZMod M) ^ 2 - 1 := by
    rw [ZMod.coe_unitOfCoprime, Int.cast_natCast, Nat.cast_sub (Nat.one_le_pow _ _ ht1), Nat.cast_pow,
      Nat.cast_one]
  have hg' : ∀ b : ZMod M, f ((g : ZMod M) * b) = 0 := by
    intro b
    have := hf (ZMod.unitOfCoprime t htco) (((Nat.gcdA (t ^ 2 - 1) M : ℤ) : ZMod M) * b)
    rwa [← mul_assoc, ← hunit, ← hbez] at this
  obtain ⟨e, he⟩ := hgcd
  ext b
  rw [AddMonoidHom.zero_apply]
  apply eq_zero_of_twentyfour_nsmul h2 h3
  rw [← map_nsmul, nsmul_eq_mul, show ((24 : ℕ) : ZMod M) = (g : ZMod M) * (e : ZMod M) by
    rw [← Nat.cast_mul, ← he], mul_assoc]
  exact hg' _

end TorusTrick

section Elementary

variable {R : Type*} [CommRing R]

def uElt (b : R) : SL(2, R) :=
  ⟨!![1, b; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

def vElt (c : R) : SL(2, R) :=
  ⟨!![1, 0; c, 1], by rw [Matrix.det_fin_two_of]; ring⟩

def hElt (t : Rˣ) : SL(2, R) :=
  ⟨!![((t⁻¹ : Rˣ) : R), 0; 0, (t : R)], by rw [Matrix.det_fin_two_of]; simp⟩

@[scoped simp] theorem uElt_coe (b : R) : (uElt b : Matrix (Fin 2) (Fin 2) R) = !![1, b; 0, 1] := rfl
@[scoped simp] theorem vElt_coe (c : R) : (vElt c : Matrix (Fin 2) (Fin 2) R) = !![1, 0; c, 1] := rfl
@[scoped simp] theorem hElt_coe (t : Rˣ) :
    (hElt t : Matrix (Fin 2) (Fin 2) R) = !![((t⁻¹ : Rˣ) : R), 0; 0, (t : R)] := rfl

theorem uElt_add (b b' : R) : uElt (b + b') = uElt b * uElt b' := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem vElt_add (c c' : R) : vElt (c + c') = vElt c * vElt c' := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem uElt_zero : uElt (0 : R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem vElt_zero : vElt (0 : R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem hElt_mul (s t : Rˣ) : hElt (s * t) = hElt s * hElt t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem hElt_one : hElt (1 : Rˣ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem hElt_inv (t : Rˣ) : (hElt t)⁻¹ = hElt t⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [← hElt_mul, mul_inv_cancel, hElt_one])

theorem hElt_inv_mul_uElt_mul_hElt (t : Rˣ) (b : R) :
    (hElt t)⁻¹ * uElt b * hElt t = uElt ((t : R) ^ 2 * b) := by
  have h1 : (t : R) * ((t⁻¹ : Rˣ) : R) = 1 := Units.mul_inv t
  rw [hElt_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.SpecialLinearGroup.coe_mul, uElt_coe, hElt_coe, inv_inv,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue, Fin.zero_eta,
      Fin.mk_one]
  · linear_combination h1
  · linear_combination
  · linear_combination
  · linear_combination h1

theorem hElt_mul_vElt_mul_hElt_inv (t : Rˣ) (c : R) :
    hElt t * vElt c * (hElt t)⁻¹ = vElt ((t : R) ^ 2 * c) := by
  have h1 : (t : R) * ((t⁻¹ : Rˣ) : R) = 1 := Units.mul_inv t
  rw [hElt_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.SpecialLinearGroup.coe_mul, vElt_coe, hElt_coe, inv_inv,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue, Fin.zero_eta,
      Fin.mk_one]
  · linear_combination h1
  · linear_combination
  · linear_combination
  · linear_combination h1

theorem uElt_mul_vElt (b c : R) (t : Rˣ) (ht : (t : R) = 1 + b * c) :
    uElt b * vElt c = vElt (c * ((t⁻¹ : Rˣ) : R)) * hElt t⁻¹ * uElt (b * ((t⁻¹ : Rˣ) : R)) := by
  have htinv : (t : R) * ((t⁻¹ : Rˣ) : R) = 1 := Units.mul_inv t
  have hkey : ((t⁻¹ : Rˣ) : R) * (1 + b * c) = 1 := by rw [← ht, Units.inv_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.SpecialLinearGroup.coe_mul, uElt_coe, vElt_coe, hElt_coe, inv_inv,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue, Fin.zero_eta,
      Fin.mk_one]
  · linear_combination -ht
  · linear_combination -b * htinv
  · linear_combination -c * htinv
  · linear_combination -(c * b * ((t⁻¹ : Rˣ) : R)) * htinv - hkey

theorem eq_vElt_mul_hElt_mul_uElt (g : SL(2, R)) (a : Rˣ)
    (ha : (g : Matrix (Fin 2) (Fin 2) R) 0 0 = a) :
    g = vElt ((g : Matrix (Fin 2) (Fin 2) R) 1 0 * ((a⁻¹ : Rˣ) : R)) * hElt a⁻¹ *
      uElt ((g : Matrix (Fin 2) (Fin 2) R) 0 1 * ((a⁻¹ : Rˣ) : R)) := by
  have hainv : (a : R) * ((a⁻¹ : Rˣ) : R) = 1 := Units.mul_inv a
  have hdet := g.det_coe
  rw [Matrix.det_fin_two, ha] at hdet
  have hkey : ((a⁻¹ : Rˣ) : R) * ((a : R) * (g : Matrix (Fin 2) (Fin 2) R) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) R) 0 1 * (g : Matrix (Fin 2) (Fin 2) R) 1 0) =
        ((a⁻¹ : Rˣ) : R) := by
    rw [hdet, mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.SpecialLinearGroup.coe_mul, uElt_coe, vElt_coe, hElt_coe, inv_inv,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue, Fin.zero_eta,
      Fin.mk_one]
  · linear_combination ha
  · linear_combination -((g : Matrix (Fin 2) (Fin 2) R) 0 1) * hainv
  · linear_combination -((g : Matrix (Fin 2) (Fin 2) R) 1 0) * hainv
  · linear_combination hkey - ((g : Matrix (Fin 2) (Fin 2) R) 1 1 +
      (g : Matrix (Fin 2) (Fin 2) R) 0 1 * (g : Matrix (Fin 2) (Fin 2) R) 1 0 * ((a⁻¹ : Rˣ) : R)) * hainv

end Elementary

section StableRange

theorem exists_isUnit_add_mul_of_ringEquiv_prod {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] (e : R ≃+* S × T)
    (hS : ∀ a c : S, IsCoprime a c → ∃ x : S, IsUnit (a + x * c))
    (hT : ∀ a c : T, IsCoprime a c → ∃ x : T, IsUnit (a + x * c)) :
    ∀ a c : R, IsCoprime a c → ∃ x : R, IsUnit (a + x * c) := by
  intro a c hac
  obtain ⟨x₁, hx₁⟩ := hS (e a).1 (e c).1 (hac.map ((RingHom.fst S T).comp e.toRingHom))
  obtain ⟨x₂, hx₂⟩ := hT (e a).2 (e c).2 (hac.map ((RingHom.snd S T).comp e.toRingHom))
  refine ⟨e.symm (x₁, x₂), ?_⟩
  have he : e (a + e.symm (x₁, x₂) * c) = ((e a).1 + x₁ * (e c).1, (e a).2 + x₂ * (e c).2) := by
    rw [map_add, map_mul, RingEquiv.apply_symm_apply]
    rfl
  obtain ⟨y₁, hy₁⟩ := hx₁.exists_right_inv
  obtain ⟨y₂, hy₂⟩ := hx₂.exists_right_inv
  have hunit : IsUnit (e (a + e.symm (x₁, x₂) * c)) := by
    rw [he]
    exact IsUnit.of_mul_eq_one (y₁, y₂) (Prod.ext hy₁ hy₂)
  simpa using hunit.map e.symm

theorem exists_isUnit_add_mul_primePow {p n : ℕ} (hp : p.Prime) (hn : 0 < n) (a c : ZMod (p ^ n))
    (hac : IsCoprime a c) : ∃ x : ZMod (p ^ n), IsUnit (a + x * c) := by
  by_cases ha : IsUnit a
  · exact ⟨0, by rwa [zero_mul, add_zero]⟩
  ·
    haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
    have hpa : p ∣ a.val := by
      by_contra h
      exact ha (by rw [← ZMod.natCast_zmod_val a]; exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp hn).mpr h)
    obtain ⟨k, hk⟩ := hpa
    have hnil : IsNilpotent a := by
      refine ⟨n, ?_⟩
      rw [← ZMod.natCast_zmod_val a, hk, Nat.cast_mul, mul_pow, ← Nat.cast_pow, ZMod.natCast_self,
        zero_mul]
    obtain ⟨u, v, huv⟩ := hac
    have hva : IsNilpotent (u * a) := by
      obtain ⟨m, hm⟩ := hnil
      exact ⟨m, by rw [mul_pow, hm, mul_zero]⟩
    have hvc : IsUnit (v * c) := by
      have : v * c = 1 - u * a := by rw [← huv]; ring
      rw [this]
      exact hva.isUnit_one_sub
    have hc : IsUnit c := isUnit_of_mul_isUnit_right hvc
    obtain ⟨w, hw⟩ := hc.exists_left_inv
    refine ⟨(1 - a) * w, ?_⟩
    rw [mul_assoc, hw, mul_one, add_sub_cancel]
    exact isUnit_one

theorem exists_isUnit_add_mul_zmod {M : ℕ} (hM : M ≠ 0) (a c : ZMod M) (hac : IsCoprime a c) :
    ∃ x : ZMod M, IsUnit (a + x * c) := by
  induction M using Nat.recOnPosPrimePosCoprime with
  | zero => exact absurd rfl hM
  | one => exact ⟨0, isUnit_of_subsingleton _⟩
  | prime_pow p n hp hn => exact exists_isUnit_add_mul_primePow hp hn a c hac
  | coprime m n hm hn hmn ihm ihn =>
    exact exists_isUnit_add_mul_of_ringEquiv_prod (ZMod.chineseRemainder hmn)
      (fun a c h => ihm (by omega) a c h) (fun a c h => ihn (by omega) a c h) a c hac

end StableRange

section CongruenceQuotient

variable (N M : ℕ)

def Gamma0Fin : Subgroup SL(2, ZMod M) where
  carrier := {g | (N : ZMod M) ∣ g 1 0}
  one_mem' := by
    simp only [Set.mem_setOf_eq, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
    exact dvd_zero _
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Matrix.SpecialLinearGroup.coe_mul] at ha hb ⊢
    rw [(Matrix.two_mul_expl a.1 b.1).2.2.1]
    exact dvd_add (ha.mul_right _) (hb.mul_left _)
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl a]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
    exact dvd_neg.mpr ha

variable {N M}

theorem mem_Gamma0Fin {g : SL(2, ZMod M)} : g ∈ Gamma0Fin N M ↔ (N : ZMod M) ∣ g 1 0 := Iff.rfl

variable (N M)

theorem castHom_apply_one_zero (hNM : N ∣ M) (g : Gamma0Fin N M) :
    ZMod.castHom hNM (ZMod N) ((g : SL(2, ZMod M)) 1 0) = 0 := by
  obtain ⟨r, hr⟩ := g.2
  rw [hr, map_mul, map_natCast, ZMod.natCast_self, zero_mul]

def gamma0FinMap (hNM : N ∣ M) : Gamma0Fin N M →* ZMod N where
  toFun g := ZMod.castHom hNM (ZMod N) ((g : SL(2, ZMod M)) 1 1)
  map_one' := by
    have h : ((1 : Gamma0Fin N M) : SL(2, ZMod M)) 1 1 = 1 := rfl
    rw [h, map_one]
  map_mul' a b := by
    have h : ((a * b : Gamma0Fin N M) : SL(2, ZMod M)) 1 1 =
        (a : SL(2, ZMod M)) 1 0 * (b : SL(2, ZMod M)) 0 1 +
          (a : SL(2, ZMod M)) 1 1 * (b : SL(2, ZMod M)) 1 1 :=
      (Matrix.two_mul_expl (a : SL(2, ZMod M)).1 (b : SL(2, ZMod M)).1).2.2.2
    rw [h, map_add, map_mul, map_mul, castHom_apply_one_zero N M hNM a, zero_mul, zero_add]

@[scoped simp]
theorem gamma0FinMap_apply (hNM : N ∣ M) (g : Gamma0Fin N M) :
    gamma0FinMap N M hNM g = ZMod.castHom hNM (ZMod N) ((g : SL(2, ZMod M)) 1 1) := rfl

def gamma0FinUnitsChar (hNM : N ∣ M) : Gamma0Fin N M →* (ZMod N)ˣ :=
  (gamma0FinMap N M hNM).toHomUnits

@[scoped simp]
theorem gamma0FinUnitsChar_coe (hNM : N ∣ M) (g : Gamma0Fin N M) :
    (gamma0FinUnitsChar N M hNM g : ZMod N) = ZMod.castHom hNM (ZMod N) ((g : SL(2, ZMod M)) 1 1) :=
  rfl

def uG (b : ZMod M) : Gamma0Fin N M :=
  ⟨uElt b, by rw [mem_Gamma0Fin, uElt_coe]; exact ⟨0, by simp⟩⟩

def vG (c : ZMod M) : Gamma0Fin N M :=
  ⟨vElt ((N : ZMod M) * c), by rw [mem_Gamma0Fin, vElt_coe]; exact ⟨c, by simp⟩⟩

def hG (t : (ZMod M)ˣ) : Gamma0Fin N M :=
  ⟨hElt t, by rw [mem_Gamma0Fin, hElt_coe]; exact ⟨0, by simp⟩⟩

@[scoped simp] theorem uG_coe (b : ZMod M) : ((uG N M b : Gamma0Fin N M) : SL(2, ZMod M)) = uElt b := rfl
@[scoped simp] theorem vG_coe (c : ZMod M) :
    ((vG N M c : Gamma0Fin N M) : SL(2, ZMod M)) = vElt ((N : ZMod M) * c) := rfl
@[scoped simp] theorem hG_coe (t : (ZMod M)ˣ) : ((hG N M t : Gamma0Fin N M) : SL(2, ZMod M)) = hElt t := rfl

theorem uG_add (b b' : ZMod M) : uG N M (b + b') = uG N M b * uG N M b' :=
  Subtype.ext (uElt_add b b')

theorem uG_zero : uG N M 0 = 1 := Subtype.ext uElt_zero

theorem vG_add (c c' : ZMod M) : vG N M (c + c') = vG N M c * vG N M c' :=
  Subtype.ext (by rw [Subgroup.coe_mul, vG_coe, vG_coe, vG_coe, mul_add, vElt_add])

theorem vG_zero : vG N M 0 = 1 := Subtype.ext (by rw [vG_coe, mul_zero, vElt_zero]; rfl)

def hGHom : (ZMod M)ˣ →* Gamma0Fin N M where
  toFun := hG N M
  map_one' := Subtype.ext hElt_one
  map_mul' s t := Subtype.ext (hElt_mul s t)

@[scoped simp] theorem hGHom_apply (t : (ZMod M)ˣ) : hGHom N M t = hG N M t := rfl

theorem hG_inv (t : (ZMod M)ˣ) : (hG N M t)⁻¹ = hG N M t⁻¹ := by
  rw [← hGHom_apply, ← map_inv, hGHom_apply]

theorem hG_inv_mul_uG_mul_hG (t : (ZMod M)ˣ) (b : ZMod M) :
    (hG N M t)⁻¹ * uG N M b * hG N M t = uG N M ((t : ZMod M) ^ 2 * b) :=
  Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hG_coe, uG_coe, uG_coe]
    exact hElt_inv_mul_uElt_mul_hElt t b)

theorem hG_mul_vG_mul_hG_inv (t : (ZMod M)ˣ) (c : ZMod M) :
    hG N M t * vG N M c * (hG N M t)⁻¹ = vG N M ((t : ZMod M) ^ 2 * c) :=
  Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hG_coe, vG_coe, vG_coe,
      mul_left_comm]
    exact hElt_mul_vElt_mul_hElt_inv t _)

theorem uG_mul_vG_one (k : ZMod M) (t : (ZMod M)ˣ) (ht : (t : ZMod M) = 1 + k * N) :
    uG N M k * vG N M 1 = vG N M ((t⁻¹ : (ZMod M)ˣ) : ZMod M) * hG N M t⁻¹ *
      uG N M (k * ((t⁻¹ : (ZMod M)ˣ) : ZMod M)) :=
  Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, uG_coe, vG_coe, vG_coe, hG_coe, uG_coe,
      mul_one]
    exact uElt_mul_vElt k (N : ZMod M) t ht)

end CongruenceQuotient

section Factor

variable {N M : ℕ} [NeZero M] (hNM : N ∣ M) {A : Type*} [AddCommGroup A]
  (h2 : ∀ a : A, a + a = 0 → a = 0) (h3 : ∀ a : A, a + a + a = 0 → a = 0)
  (Φ : Gamma0Fin N M →* Multiplicative A)

include h2 h3

theorem map_uG_eq_one (b : ZMod M) : Φ (uG N M b) = 1 := by
  let f : ZMod M →+ A :=
    { toFun := fun b => Multiplicative.toAdd (Φ (uG N M b))
      map_zero' := by simp only [uG_zero, map_one, toAdd_one]
      map_add' := fun b b' => by simp only [uG_add, map_mul, toAdd_mul] }
  have hf : ∀ (t : (ZMod M)ˣ) (b : ZMod M), f (((t : ZMod M) ^ 2 - 1) * b) = 0 := by
    intro t b
    have key : Φ (uG N M ((t : ZMod M) ^ 2 * b)) = Φ (uG N M b) := by
      rw [← hG_inv_mul_uG_mul_hG, map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
    rw [sub_mul, one_mul, map_sub, sub_eq_zero]
    show Multiplicative.toAdd (Φ (uG N M ((t : ZMod M) ^ 2 * b))) = Multiplicative.toAdd (Φ (uG N M b))
    rw [key]
  have h0 := addMonoidHom_zmod_eq_zero_of_units h2 h3 f hf
  have : f b = 0 := by rw [h0]; rfl
  exact toAdd_eq_zero.mp this

theorem map_vG_eq_one (c : ZMod M) : Φ (vG N M c) = 1 := by
  let f : ZMod M →+ A :=
    { toFun := fun c => Multiplicative.toAdd (Φ (vG N M c))
      map_zero' := by simp only [vG_zero, map_one, toAdd_one]
      map_add' := fun c c' => by simp only [vG_add, map_mul, toAdd_mul] }
  have hf : ∀ (t : (ZMod M)ˣ) (c : ZMod M), f (((t : ZMod M) ^ 2 - 1) * c) = 0 := by
    intro t c
    have key : Φ (vG N M ((t : ZMod M) ^ 2 * c)) = Φ (vG N M c) := by
      rw [← hG_mul_vG_mul_hG_inv, map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]
    rw [sub_mul, one_mul, map_sub, sub_eq_zero]
    show Multiplicative.toAdd (Φ (vG N M ((t : ZMod M) ^ 2 * c))) = Multiplicative.toAdd (Φ (vG N M c))
    rw [key]
  have h0 := addMonoidHom_zmod_eq_zero_of_units h2 h3 f hf
  have : f c = 0 := by rw [h0]; rfl
  exact toAdd_eq_zero.mp this

theorem map_hG_eq_one_of_cast_eq_one (t : (ZMod M)ˣ)
    (ht : ZMod.castHom hNM (ZMod N) (t : ZMod M) = 1) : Φ (hG N M t) = 1 := by

  have hN0 : ZMod.castHom hNM (ZMod N) ((t : ZMod M) - 1) = 0 := by rw [map_sub, ht, map_one, sub_self]
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at hN0
  obtain ⟨k, hk⟩ := hN0
  have htk : (t : ZMod M) = 1 + (k : ZMod M) * N := by
    have : (t : ZMod M) - 1 = (((t : ZMod M) - 1).val : ZMod M) := (ZMod.natCast_zmod_val _).symm
    rw [hk, Nat.cast_mul, mul_comm] at this
    rw [← this, add_sub_cancel]
  have hsteinberg := congrArg Φ (uG_mul_vG_one N M (k : ZMod M) t htk)
  rw [map_mul, map_mul, map_mul, map_uG_eq_one h2 h3, map_uG_eq_one h2 h3, map_vG_eq_one h2 h3,
    map_vG_eq_one h2 h3, one_mul, one_mul, mul_one, ← hG_inv, map_inv] at hsteinberg
  exact inv_eq_one.mp hsteinberg.symm

omit [NeZero M] h2 h3 in
theorem uG_mul_apply_zero_zero (x : ZMod M) (g : Gamma0Fin N M) :
    ((uG N M x * g : Gamma0Fin N M) : SL(2, ZMod M)) 0 0 =
      (g : SL(2, ZMod M)) 0 0 + x * (g : SL(2, ZMod M)) 1 0 := by
  rw [Subgroup.coe_mul, uG_coe, Matrix.SpecialLinearGroup.coe_mul]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [NeZero M] h2 h3 in
theorem uG_mul_apply_one_zero (x : ZMod M) (g : Gamma0Fin N M) :
    ((uG N M x * g : Gamma0Fin N M) : SL(2, ZMod M)) 1 0 = (g : SL(2, ZMod M)) 1 0 := by
  rw [Subgroup.coe_mul, uG_coe, Matrix.SpecialLinearGroup.coe_mul]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [NeZero M] h2 h3 in
theorem uG_mul_apply_one_one (x : ZMod M) (g : Gamma0Fin N M) :
    ((uG N M x * g : Gamma0Fin N M) : SL(2, ZMod M)) 1 1 = (g : SL(2, ZMod M)) 1 1 := by
  rw [Subgroup.coe_mul, uG_coe, Matrix.SpecialLinearGroup.coe_mul]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem map_eq_map_hG_of_isUnit (g : Gamma0Fin N M) (a : (ZMod M)ˣ)
    (ha : (g : SL(2, ZMod M)) 0 0 = a) : Φ g = Φ (hG N M a⁻¹) := by
  obtain ⟨r, hr⟩ := g.2
  have hbruhat := eq_vElt_mul_hElt_mul_uElt (g : SL(2, ZMod M)) a ha
  have hG' : g = vG N M (r * ((a⁻¹ : (ZMod M)ˣ) : ZMod M)) * hG N M a⁻¹ *
      uG N M ((g : SL(2, ZMod M)) 0 1 * ((a⁻¹ : (ZMod M)ˣ) : ZMod M)) := by
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, vG_coe, hG_coe, uG_coe, ← mul_assoc (N : ZMod M), ← hr]
    exact hbruhat
  rw [hG', map_mul, map_mul, map_uG_eq_one h2 h3, map_vG_eq_one h2 h3, one_mul, mul_one]

theorem gamma0Fin_hom_factor :
    ∃ χ : (ZMod N)ˣ →* Multiplicative A, Φ = χ.comp (gamma0FinUnitsChar N M hNM) := by
  have hM : M ≠ 0 := NeZero.ne M

  set ψ : (ZMod M)ˣ →* Multiplicative A := Φ.comp (hGHom N M) with hψ
  have hker : (ZMod.unitsMap hNM).ker ≤ ψ.ker := by
    intro t ht
    rw [MonoidHom.mem_ker] at ht ⊢
    have ht' : ZMod.castHom hNM (ZMod N) (t : ZMod M) = 1 := by
      have := congrArg (fun u : (ZMod N)ˣ => (u : ZMod N)) ht
      simpa [ZMod.unitsMap, Units.coe_map] using this
    rw [hψ, MonoidHom.comp_apply, hGHom_apply]
    exact map_hG_eq_one_of_cast_eq_one hNM h2 h3 Φ t ht'
  have hsurj := ZMod.unitsMap_surjective (n := N) (m := M) hNM
  let χ : (ZMod N)ˣ →* Multiplicative A :=
    (ZMod.unitsMap hNM).liftOfRightInverse (Function.surjInv hsurj)
      (Function.rightInverse_surjInv hsurj) ⟨ψ, hker⟩
  have hχ : ∀ t : (ZMod M)ˣ, χ (ZMod.unitsMap hNM t) = Φ (hG N M t) := by
    intro t
    exact (ZMod.unitsMap hNM).liftOfRightInverse_comp_apply (Function.surjInv hsurj)
      (Function.rightInverse_surjInv hsurj) ⟨ψ, hker⟩ t
  refine ⟨χ, MonoidHom.ext fun g => ?_⟩

  have hcop : IsCoprime ((g : SL(2, ZMod M)) 0 0) ((g : SL(2, ZMod M)) 1 0) := by
    refine ⟨(g : SL(2, ZMod M)) 1 1, -((g : SL(2, ZMod M)) 0 1), ?_⟩
    have hdet := (g : SL(2, ZMod M)).det_coe
    rw [Matrix.det_fin_two] at hdet
    linear_combination hdet
  obtain ⟨x, hx⟩ := exists_isUnit_add_mul_zmod hM _ _ hcop
  set s : (ZMod M)ˣ := hx.unit with hs
  set g' : Gamma0Fin N M := uG N M x * g with hg'
  have hs0 : ((g' : Gamma0Fin N M) : SL(2, ZMod M)) 0 0 = s := by
    rw [hg', uG_mul_apply_zero_zero, hs, IsUnit.unit_spec]
  have hΦ : Φ g = Φ (hG N M s⁻¹) := by
    rw [← map_eq_map_hG_of_isUnit h2 h3 Φ g' s hs0, hg', map_mul, map_uG_eq_one h2 h3, one_mul]

  have hchar : gamma0FinUnitsChar N M hNM g = (ZMod.unitsMap hNM s)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    ext
    rw [Units.val_mul, gamma0FinUnitsChar_coe, Units.val_one]
    have hdet := ((g' : Gamma0Fin N M) : SL(2, ZMod M)).det_coe
    rw [Matrix.det_fin_two, hs0, hg', uG_mul_apply_one_one, uG_mul_apply_one_zero] at hdet
    have := congrArg (ZMod.castHom hNM (ZMod N)) hdet
    rw [map_sub, map_mul, map_mul, castHom_apply_one_zero N M hNM g, mul_zero, sub_zero, map_one,
      mul_comm] at this
    simpa [ZMod.unitsMap, Units.coe_map] using this
  rw [MonoidHom.comp_apply, hchar, ← map_inv, hχ, hΦ]

end Factor

end Ihara
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

end Inl_A3_CongruenceQuotientKill
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

section Inl_P2A_TorusElements

namespace Ihara
p2m_export "Ihara" "HasTrivialSchurMultiplier hasTrivialSchurMultiplier_of_subsingleton exists_pow_prime_pow_eq_one_of_sl2_stem"
p2m_open "Ihara"

section CoeTwinsT

open scoped MatrixGroups

private theorem sl2coeT_mul {R : Type*} [CommRing R] (A B : SL(2, R)) :
    ((A * B : SL(2, R)) : Matrix (Fin 2) (Fin 2) R)
      = (A : Matrix (Fin 2) (Fin 2) R) * (B : Matrix (Fin 2) (Fin 2) R) := rfl

private theorem sl2coeT_one {R : Type*} [CommRing R] :
    ((1 : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = 1 := rfl

private theorem sl2coeT_pow {R : Type*} [CommRing R] (A : SL(2, R)) (n : ℕ) :
    ((A ^ n : SL(2, R)) : Matrix (Fin 2) (Fin 2) R)
      = (A : Matrix (Fin 2) (Fin 2) R) ^ n := by
  induction n with
  | zero => rfl
  | succ m ih => rw [pow_succ, sl2coeT_mul, ih, pow_succ]

end CoeTwinsT
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

open Matrix

open scoped MatrixGroups

section UnitOfOrder

variable (q : ℕ) (n : ℕ)

theorem exists_units_orderOf_eq_sub_one (hq : q.Prime) (hq2 : q ≠ 2) (hn : n ≠ 0) :
    ∃ ζ : (ZMod (q ^ n))ˣ, orderOf ζ = q - 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : IsCyclic (ZMod (q ^ n))ˣ := ZMod.isCyclic_units_of_prime_pow q hq hq2 n
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod (q ^ n))ˣ)
  have hcard : Nat.card (ZMod (q ^ n))ˣ = q ^ (n - 1) * (q - 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow hq (Nat.pos_of_ne_zero hn)]
  have hgord : orderOf g = q ^ (n - 1) * (q - 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  refine ⟨g ^ q ^ (n - 1), ?_⟩
  rw [orderOf_pow, hgord, Nat.gcd_eq_right ⟨q - 1, rfl⟩,
    Nat.mul_div_cancel_left _ (pow_pos hq.pos _)]

variable {q n}

def diagTorusGen (ζ : (ZMod (q ^ n))ˣ) : SL(2, ZMod (q ^ n)) :=
  ⟨!![(ζ : ZMod (q ^ n)), 0; 0, ((ζ⁻¹ : (ZMod (q ^ n))ˣ) : ZMod (q ^ n))], by
    rw [Matrix.det_fin_two_of]
    simp⟩

theorem diagTorusGen_pow_coe (ζ : (ZMod (q ^ n))ˣ) (k : ℕ) :
    ((diagTorusGen ζ ^ k : SL(2, ZMod (q ^ n))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ n)))
      = !![((ζ ^ k : (ZMod (q ^ n))ˣ) : ZMod (q ^ n)), 0;
           0, (((ζ ^ k)⁻¹ : (ZMod (q ^ n))ˣ) : ZMod (q ^ n))] := by
  induction k with
  | zero => simp [Matrix.one_fin_two]
  | succ m ih =>
    rw [pow_succ, sl2coeT_mul, ih, diagTorusGen, Matrix.mul_fin_two]
    push_cast [pow_succ, _root_.mul_inv_rev]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_comm]

theorem orderOf_diagTorusGen (ζ : (ZMod (q ^ n))ˣ) :
    orderOf (diagTorusGen ζ) = orderOf ζ := by
  apply orderOf_eq_orderOf_iff.mpr
  intro k
  constructor
  · intro hk
    have := congrArg (fun M : SL(2, ZMod (q ^ n)) =>
      (M : Matrix (Fin 2) (Fin 2) (ZMod (q ^ n))) 0 0) hk
    simp only [diagTorusGen_pow_coe] at this
    have h00 : ((ζ ^ k : (ZMod (q ^ n))ˣ) : ZMod (q ^ n)) = 1 := by
      simpa [Matrix.one_fin_two] using this
    exact Units.ext h00
  · intro hk
    apply Subtype.ext
    rw [diagTorusGen_pow_coe, hk]
    simp [Matrix.one_fin_two]

end UnitOfOrder
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

section CongruenceKernelExponent

variable {R : Type*} [CommRing R]

theorem one_add_smul_pow (m : ℕ) (x : R) (A : Matrix (Fin 2) (Fin 2) R) :
    ∃ B : Matrix (Fin 2) (Fin 2) R,
      (1 + x • A) ^ m = 1 + ((m : R) * x) • A + x ^ 2 • B := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ l ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨(l : R) • (A * A) + B + x • (B * A), ?_⟩
    rw [pow_succ, hB]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
      mul_smul_comm, smul_add, smul_smul]
    module

theorem pow_prime_level_succ {q n : ℕ} {m : ℕ} (hm : m ≠ 0)
    (A : Matrix (Fin 2) (Fin 2) (ZMod (q ^ n))) :
    ∃ B : Matrix (Fin 2) (Fin 2) (ZMod (q ^ n)),
      (1 + ((q : ZMod (q ^ n)) ^ m) • A) ^ q = 1 + ((q : ZMod (q ^ n)) ^ (m + 1)) • B := by
  obtain ⟨B, hB⟩ := one_add_smul_pow q ((q : ZMod (q ^ n)) ^ m) A
  refine ⟨A + ((q : ZMod (q ^ n)) ^ (m - 1)) • B, ?_⟩
  rw [hB]
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  have h1 : ((q : ℕ) : ZMod (q ^ n)) * (q : ZMod (q ^ n)) ^ (l + 1)
      = (q : ZMod (q ^ n)) ^ (l + 1 + 1) := by
    ring
  have h2 : ((q : ZMod (q ^ n)) ^ (l + 1)) ^ 2
      = (q : ZMod (q ^ n)) ^ (l + 1 + 1) * (q : ZMod (q ^ n)) ^ l := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [h1, h2, add_assoc, mul_smul, ← smul_add, Nat.succ_sub_one]

theorem congKernel_pow_card_eq_one {q n : ℕ} (hn : n ≠ 0)
    (M : SL(2, ZMod (q ^ n))) (A : Matrix (Fin 2) (Fin 2) (ZMod (q ^ n)))
    (hM : (M : Matrix (Fin 2) (Fin 2) (ZMod (q ^ n))) = 1 + (q : ZMod (q ^ n)) • A) :
    M ^ q ^ (n - 1) = 1 := by

  suffices h : ∀ e : ℕ, ∃ B : Matrix (Fin 2) (Fin 2) (ZMod (q ^ n)),
      ((M ^ q ^ e : SL(2, ZMod (q ^ n))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ n)))
        = 1 + ((q : ZMod (q ^ n)) ^ (e + 1)) • B by
    obtain ⟨B, hB⟩ := h (n - 1)
    have hlevel : (q : ZMod (q ^ n)) ^ (n - 1 + 1) = 0 := by
      rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
      rw [← Nat.cast_pow, ZMod.natCast_self]
    apply Subtype.ext
    rw [hB, hlevel, zero_smul, add_zero, sl2coeT_one]
  intro e
  induction e with
  | zero =>
    exact ⟨A, by rw [pow_zero, pow_one, hM, pow_one]⟩
  | succ f ih =>
    obtain ⟨B, hB⟩ := ih
    obtain ⟨B', hB'⟩ := pow_prime_level_succ (n := n) (q := q) (Nat.succ_ne_zero f) B
    refine ⟨B', ?_⟩
    rw [pow_succ, pow_mul, sl2coeT_pow, hB, hB']

end CongruenceKernelExponent
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

section LiftAndPower

variable {q n : ℕ}

def slReduceToBase (q n : ℕ) (hn : n ≠ 0) :
    SL(2, ZMod (q ^ n)) →* SL(2, ZMod q) :=
  SpecialLinearGroup.map (ZMod.castHom (dvd_pow_self q hn) (ZMod q))

theorem orderOf_pow_card_eq_of_reduction (hq : q.Prime) (hn : n ≠ 0)
    (M : SL(2, ZMod (q ^ n)))
    (hred : orderOf (slReduceToBase q n hn M) = q + 1)
    (hker : ∀ P : SL(2, ZMod (q ^ n)), slReduceToBase q n hn P = 1 →
      ∃ A, (P : Matrix (Fin 2) (Fin 2) (ZMod (q ^ n))) = 1 + (q : ZMod (q ^ n)) • A) :
    orderOf (M ^ q ^ (n - 1)) = q + 1 := by
  haveI : NeZero q := ⟨hq.ne_zero⟩

  have hNpow : (M ^ q ^ (n - 1)) ^ (q + 1) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    have hMk : slReduceToBase q n hn (M ^ (q + 1)) = 1 := by
      rw [map_pow, ← hred, pow_orderOf_eq_one]
    obtain ⟨A, hA⟩ := hker _ hMk
    exact congKernel_pow_card_eq_one hn _ A hA

  have hdvd1 : orderOf (M ^ q ^ (n - 1)) ∣ q + 1 := orderOf_dvd_of_pow_eq_one hNpow
  have hdvd2 : (q + 1) ∣ orderOf (M ^ q ^ (n - 1)) := by
    have hmap : orderOf (slReduceToBase q n hn (M ^ q ^ (n - 1)))
        ∣ orderOf (M ^ q ^ (n - 1)) := orderOf_map_dvd (slReduceToBase q n hn) (M ^ q ^ (n - 1))
    have hredN : orderOf (slReduceToBase q n hn (M ^ q ^ (n - 1))) = q + 1 := by
      rw [map_pow, orderOf_pow, hred]
      have hgcd : (q + 1).gcd (q ^ (n - 1)) = 1 := by
        have : (q + 1).Coprime q := by
          rw [add_comm]
          exact Nat.coprime_add_self_left.mpr (Nat.gcd_one_left q)
        exact Nat.Coprime.pow_right _ this
      rw [hgcd, Nat.div_one]
    rwa [hredN] at hmap
  exact Nat.dvd_antisymm hdvd1 hdvd2

end LiftAndPower
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

end Ihara
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

end Inl_P2A_TorusElements
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

section Inl_A3_SL2Surjective

namespace Ihara
p2m_export "Ihara" "HasTrivialSchurMultiplier hasTrivialSchurMultiplier_of_subsingleton exists_pow_prime_pow_eq_one_of_sl2_stem"
p2m_open "Ihara"

open Matrix

open scoped MatrixGroups

section ArithmeticLemmas

private lemma natCast_dvd_int {p : ℕ} {z : ℤ} : (p : ℤ) ∣ z ↔ p ∣ z.natAbs :=
  Int.natCast_dvd

private def primeSel (c d : ℤ) : ℕ :=
  ∏ p ∈ c.natAbs.primeFactors, if p ∣ d.natAbs then 1 else p

private lemma dvd_primeSel {c d : ℤ} {p : ℕ} (hc : c ≠ 0) (hp : p.Prime)
    (hpc : (p : ℤ) ∣ c) (hpd : ¬(p : ℤ) ∣ d) : p ∣ primeSel c d := by
  have hmem : p ∈ c.natAbs.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, natCast_dvd_int.mp hpc, Int.natAbs_ne_zero.mpr hc⟩
  have h := Finset.dvd_prod_of_mem (fun q : ℕ => if q ∣ d.natAbs then 1 else q) hmem
  simp only [if_neg (fun hcontra => hpd (natCast_dvd_int.mpr hcontra))] at h
  exact h

private lemma not_dvd_primeSel {c d : ℤ} {p : ℕ} (hp : p.Prime) (hpd : (p : ℤ) ∣ d) :
    ¬p ∣ primeSel c d := by
  intro hdvd
  obtain ⟨q, hq, hpq⟩ := (Nat.Prime.prime hp).dvd_finsetProd_iff _ |>.mp hdvd
  by_cases hqd : q ∣ d.natAbs
  · rw [if_pos hqd] at hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpq)
  · rw [if_neg hqd] at hpq
    have hq' : q.Prime := (Nat.mem_primeFactors.mp hq).1
    exact hqd (((Nat.prime_dvd_prime_iff_eq hp hq').mp hpq) ▸ natCast_dvd_int.mp hpd)

theorem exists_coprime_lift (N : ℕ) [NeZero N] {c₀ d₀ : ℤ}
    (H : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c₀ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ)) :
    ∃ γ δ : ℤ, Int.gcd γ δ = 1 ∧
      (γ : ZMod N) = (c₀ : ZMod N) ∧ (δ : ZMod N) = (d₀ : ZMod N) := by

  set γ : ℤ := if c₀ = 0 then (N : ℤ) else c₀ with hγ_def
  have hγ0 : γ ≠ 0 := by
    rw [hγ_def]
    split
    · exact_mod_cast NeZero.ne N
    · assumption
  have hγc : (γ : ZMod N) = (c₀ : ZMod N) := by
    rw [hγ_def]
    split
    · next h => simp [h]
    · rfl
  have Hγ : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ γ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ) := by
    intro p pp hpγ hpd
    refine H p pp ?_ hpd
    rw [hγ_def] at hpγ
    by_cases h : c₀ = 0
    · simp [h]
    · rwa [if_neg h] at hpγ

  refine ⟨γ, d₀ + (primeSel γ d₀ : ℤ) * (N : ℤ), ?_, hγc, ?_⟩
  ·
    by_contra hne
    obtain ⟨p, pp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have h1 : (p : ℤ) ∣ γ :=
      natCast_dvd_int.mpr (hpdvd.trans (Nat.gcd_dvd_left _ _))
    have h2 : (p : ℤ) ∣ d₀ + (primeSel γ d₀ : ℤ) * (N : ℤ) :=
      natCast_dvd_int.mpr (hpdvd.trans (Nat.gcd_dvd_right _ _))
    by_cases hpd : (p : ℤ) ∣ d₀
    ·
      have h3 : (p : ℤ) ∣ (primeSel γ d₀ : ℤ) * (N : ℤ) := by
        have := h2.sub hpd
        rwa [add_sub_cancel_left] at this
      rcases (Nat.prime_iff_prime_int.mp pp).dvd_or_dvd h3 with h4 | h4
      · exact not_dvd_primeSel pp hpd (natCast_dvd_int.mp h4)
      · exact Hγ p pp h1 hpd h4
    ·
      have h3 : (p : ℤ) ∣ (primeSel γ d₀ : ℤ) :=
        natCast_dvd_int.mpr (dvd_primeSel hγ0 pp h1 hpd)
      refine hpd ?_
      have := h2.sub (h3.mul_right (N : ℤ))
      rwa [add_sub_cancel_right] at this
  ·
    push_cast
    simp

end ArithmeticLemmas
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

section Lifting

theorem exists_sl2_int_lift {N : ℕ} [NeZero N] {a b c d : ZMod N}
    (h : a * d - b * c = 1) :
    ∃ α β γ δ : ℤ, α * δ - β * γ = 1 ∧
      (α : ZMod N) = a ∧ (β : ZMod N) = b ∧ (γ : ZMod N) = c ∧ (δ : ZMod N) = d := by

  set a₀ : ℤ := ZMod.cast a with ha₀
  set b₀ : ℤ := ZMod.cast b with hb₀
  set c₀ : ℤ := ZMod.cast c with hc₀
  set d₀ : ℤ := ZMod.cast d with hd₀
  have hcasta : ((a₀ : ℤ) : ZMod N) = a := ZMod.intCast_zmod_cast a
  have hcastb : ((b₀ : ℤ) : ZMod N) = b := ZMod.intCast_zmod_cast b
  have hcastc : ((c₀ : ℤ) : ZMod N) = c := ZMod.intCast_zmod_cast c
  have hcastd : ((d₀ : ℤ) : ZMod N) = d := ZMod.intCast_zmod_cast d

  have hdvd : (N : ℤ) ∣ a₀ * d₀ - b₀ * c₀ - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hcasta, hcastb, hcastc, hcastd]
    rw [sub_eq_zero]
    exact h

  have H : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c₀ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ) := by
    intro p pp hpc hpd hpN
    have hone : (p : ℤ) ∣ 1 := by
      have h1 : (p : ℤ) ∣ a₀ * d₀ - b₀ * c₀ - 1 := hpN.trans hdvd
      have h2 : (p : ℤ) ∣ a₀ * d₀ := hpd.mul_left a₀
      have h3 : (p : ℤ) ∣ b₀ * c₀ := hpc.mul_left b₀
      have key : (1 : ℤ) = a₀ * d₀ - b₀ * c₀ - (a₀ * d₀ - b₀ * c₀ - 1) := by ring
      rw [key]
      exact (h2.sub h3).sub h1
    exact pp.one_lt.ne' (Nat.dvd_one.mp (by exact_mod_cast hone))

  obtain ⟨γ, δ, hγδ, hγ, hδ⟩ := exists_coprime_lift N H
  rw [hcastc] at hγ
  rw [hcastd] at hδ

  set α₀ : ℤ := Int.gcdB γ δ with hα₀
  set β₀ : ℤ := -Int.gcdA γ δ with hβ₀
  have hdet₀ : α₀ * δ - β₀ * γ = 1 := by
    have hbez := Int.gcd_eq_gcd_ab γ δ
    rw [hγδ] at hbez
    push_cast at hbez
    rw [hα₀, hβ₀]
    linear_combination -hbez

  have hdet₀' : (α₀ : ZMod N) * d - (β₀ : ZMod N) * c = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod N)) hdet₀
    push_cast at this
    rwa [hγ, hδ] at this

  set lam : ZMod N := b * (α₀ : ZMod N) - a * (β₀ : ZMod N) with hlam
  set l : ℤ := ZMod.cast lam with hl
  have hcastl : ((l : ℤ) : ZMod N) = lam := ZMod.intCast_zmod_cast lam
  refine ⟨α₀ + l * γ, β₀ + l * δ, γ, δ, ?_, ?_, ?_, hγ, hδ⟩
  · linear_combination hdet₀
  ·
    push_cast
    rw [hcastl, hγ, hlam]
    linear_combination (-(α₀ : ZMod N)) * h + a * hdet₀'
  ·
    push_cast
    rw [hcastl, hδ, hlam]
    linear_combination (-(β₀ : ZMod N)) * h + b * hdet₀'

theorem SL2_reduction_surjective (N : ℕ) [NeZero N] :
    Function.Surjective
      (SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N))) := by
  intro M
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have hM := M.prop
    rwa [Matrix.det_fin_two] at hM
  obtain ⟨α, β, γ, δ, h1, ha, hb, hc, hd⟩ := exists_sl2_int_lift hdet
  refine ⟨⟨!![α, β; γ, δ], by rw [Matrix.det_fin_two_of]; exact h1⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simpa [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
      using ‹_›

end Lifting
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

end Ihara
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

end Inl_A3_SL2Surjective
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

section Inl_P2B_BinomialTwin

set_option autoImplicit false

namespace Ihara
p2m_export "Ihara" "HasTrivialSchurMultiplier hasTrivialSchurMultiplier_of_subsingleton exists_pow_prime_pow_eq_one_of_sl2_stem"
p2m_open "Ihara"

section ThreeTermBinomial

variable {R : Type*} [CommRing R]

theorem one_add_smul_pow_three (n : ℕ) (c : R) (A : Matrix (Fin 2) (Fin 2) R) :
    ∃ B : Matrix (Fin 2) (Fin 2) R, (1 + c • A) ^ n =
      1 + ((n : R) * c) • A + (((n.choose 2 : ℕ) : R) * c ^ 2) • (A * A) + c ^ 3 • B := by
  induction n with
  | zero =>
    refine ⟨0, ?_⟩
    simp [Nat.choose_eq_zero_of_lt (show 0 < 2 from Nat.zero_lt_two)]
  | succ l ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨((l.choose 2 : ℕ) : R) • (A * A * A) + B + c • (B * A), ?_⟩
    have hc2 : (l + 1).choose 2 = l.choose 2 + l := by
      have := Nat.choose_succ_succ' l 1
      simpa [Nat.choose_one_right, add_comm] using this
    rw [pow_succ, hB, hc2]
    simp only [Nat.cast_add, Nat.cast_succ, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
      mul_smul_comm, smul_add, smul_smul]
    module

end ThreeTermBinomial
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

theorem one_add_smul_pow_eq_of_odd (q m : ℕ) (hq : Odd q) (hm : 3 ≤ m)
    (A : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) :
    (1 + ((q : ZMod (q ^ m)) ^ (m - 2)) • A) ^ q
      = 1 + ((q : ZMod (q ^ m)) ^ (m - 1)) • A := by
  obtain ⟨B, hB⟩ := one_add_smul_pow_three q ((q : ZMod (q ^ m)) ^ (m - 2)) A

  have hqm : (q : ZMod (q ^ m)) ^ m = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have hvan : ∀ k : ℕ, m ≤ k → (q : ZMod (q ^ m)) ^ k = 0 := fun k hk => by
    rw [show k = m + (k - m) by omega, pow_add, hqm, zero_mul]
  have h1 : (q : ZMod (q ^ m)) * (q : ZMod (q ^ m)) ^ (m - 2) = (q : ZMod (q ^ m)) ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h2 : ((q.choose 2 : ℕ) : ZMod (q ^ m)) * ((q : ZMod (q ^ m)) ^ (m - 2)) ^ 2 = 0 := by
    obtain ⟨k, hk⟩ := hq
    have hc : q.choose 2 = q * k := by
      rw [Nat.choose_two_right, hk, show 2 * k + 1 - 1 = 2 * k by omega,
        show (2 * k + 1) * (2 * k) = 2 * ((2 * k + 1) * k) by ring,
        Nat.mul_div_cancel_left _ Nat.zero_lt_two]
    rw [hc, Nat.cast_mul, mul_comm ((q : ℕ) : ZMod (q ^ m)) ((k : ℕ) : ZMod (q ^ m)), mul_assoc,
      ← pow_mul, ← pow_succ', hvan _ (by omega), mul_zero]
  have h3 : ((q : ZMod (q ^ m)) ^ (m - 2)) ^ 3 = 0 := by
    rw [← pow_mul]
    exact hvan _ (by omega)
  rw [hB, h1, h2, h3]
  simp only [zero_smul, add_zero]

theorem one_add_smul_pow_prime_eq (q m : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hm : 3 ≤ m)
    (A : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) :
    (1 + ((q : ZMod (q ^ m)) ^ (m - 2)) • A) ^ q
      = 1 + ((q : ZMod (q ^ m)) ^ (m - 1)) • A :=
  one_add_smul_pow_eq_of_odd q m (hq.odd_of_ne_two hq2) hm A

end Ihara
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

end Inl_P2B_BinomialTwin
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

section Inl_P2B_Filtration

set_option autoImplicit false
set_option Elab.async false

namespace Ihara
p2m_export "Ihara" "HasTrivialSchurMultiplier hasTrivialSchurMultiplier_of_subsingleton exists_pow_prime_pow_eq_one_of_sl2_stem"
p2m_open "Ihara"

open Matrix
open scoped MatrixGroups

noncomputable section

variable (q m : ℕ)

section sl2coe
variable {R : Type*} [CommRing R]
private theorem sl2coe_mul (A B : SL(2, R)) :
    ((A * B : SL(2, R)) : Matrix (Fin 2) (Fin 2) R)
      = (A : Matrix (Fin 2) (Fin 2) R) * B := rfl
private theorem sl2coe_one :
    ((1 : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = 1 := rfl
private theorem sl2coe_pow (A : SL(2, R)) (n : ℕ) :
    ((A ^ n : SL(2, R)) : Matrix (Fin 2) (Fin 2) R)
      = (A : Matrix (Fin 2) (Fin 2) R) ^ n := rfl
end sl2coe
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

def congFilt (a : ℕ) : Subgroup SL(2, ZMod (q ^ m)) where
  carrier := {g | ∃ A : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m)),
    (g : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) = 1 + ((q : ZMod (q ^ m)) ^ a) • A}
  one_mem' := ⟨0, by simp⟩
  mul_mem' := by
    rintro x y ⟨A, hA⟩ ⟨B, hB⟩
    refine ⟨A + B + ((q : ZMod (q ^ m)) ^ a) • (A * B), ?_⟩
    rw [sl2coe_mul]
    rw [hA, hB]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_add, smul_mul_assoc,
      mul_smul_comm, smul_smul]
    abel
  inv_mem' := by
    rintro x ⟨A, hA⟩

    refine ⟨-(A * ((x⁻¹ : SL(2, ZMod (q ^ m))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m)))),
      ?_⟩
    have h1 : (1 + ((q : ZMod (q ^ m)) ^ a) • A)
        * ((x⁻¹ : SL(2, ZMod (q ^ m))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) = 1 := by
      rw [← hA, ← sl2coe_mul, mul_inv_cancel,
        sl2coe_one]
    rw [add_mul, one_mul, smul_mul_assoc] at h1
    rw [smul_neg, ← sub_eq_add_neg, eq_sub_iff_add_eq]
    exact h1

theorem mem_congFilt_iff {a : ℕ} {g : SL(2, ZMod (q ^ m))} :
    g ∈ congFilt q m a ↔ ∃ A : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m)),
      (g : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) = 1 + ((q : ZMod (q ^ m)) ^ a) • A :=
  Iff.rfl

scoped instance congFilt_normal (a : ℕ) : (congFilt q m a).Normal where
  conj_mem := by
    rintro g ⟨A, hA⟩ x
    refine ⟨(x : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) * A
      * ((x⁻¹ : SL(2, ZMod (q ^ m))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))), ?_⟩
    rw [sl2coe_mul, sl2coe_mul]
    rw [hA, mul_add, mul_one, add_mul, mul_smul_comm, smul_mul_assoc]
    rw [← sl2coe_mul, mul_inv_cancel, sl2coe_one]

@[scoped simp] theorem congFilt_zero : congFilt q m 0 = ⊤ := by
  ext g; simp only [mem_congFilt_iff, pow_zero, one_smul, Subgroup.mem_top, iff_true]
  exact ⟨(g : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) - 1, by rw [add_sub_cancel]⟩

theorem congFilt_of_self_le {a : ℕ} (ha : m ≤ a) : congFilt q m a = ⊥ := by
  ext g
  simp only [mem_congFilt_iff, Subgroup.mem_bot]
  constructor
  · rintro ⟨A, hA⟩
    have hq0 : ((q : ZMod (q ^ m)) ^ a) = 0 := by
      have h1 : ((q : ZMod (q ^ m)) ^ m) = 0 := by
        have : ((q ^ m : ℕ) : ZMod (q ^ m)) = 0 := ZMod.natCast_self (q ^ m)
        rwa [Nat.cast_pow] at this
      calc ((q : ZMod (q ^ m)) ^ a) = (q : ZMod (q ^ m)) ^ m * (q : ZMod (q ^ m)) ^ (a - m) := by
            rw [← pow_add, Nat.add_sub_cancel' ha]
        _ = 0 := by rw [h1, zero_mul]
    rw [hq0, zero_smul, add_zero] at hA
    ext i j
    rw [show ((1 : SL(2, ZMod (q^m))) : Matrix _ _ _) i j
        = (1 : Matrix (Fin 2) (Fin 2) (ZMod (q^m))) i j from rfl, ← hA]
  · rintro rfl; exact ⟨0, by simp⟩

theorem congFilt_antitone {a b : ℕ} (hab : a ≤ b) : congFilt q m b ≤ congFilt q m a := by
  rintro g ⟨A, hA⟩
  exact ⟨((q : ZMod (q ^ m)) ^ (b - a)) • A, by
    rw [hA, smul_smul, ← pow_add, Nat.add_sub_cancel' hab]⟩

def slReduceLevel (a : ℕ) (ha : a ≤ m) :
    SL(2, ZMod (q ^ m)) →* SL(2, ZMod (q ^ a)) :=
  SpecialLinearGroup.map (ZMod.castHom (pow_dvd_pow q ha) (ZMod (q ^ a)))

theorem congFilt_eq_ker_reduceLevel {a : ℕ} (ha : a ≤ m) [NeZero q] :
    congFilt q m a = (slReduceLevel q m a ha).ker := by
  haveI : NeZero (q ^ m) := ⟨pow_ne_zero m (NeZero.ne q)⟩
  have hqa0 : ((q : ZMod (q ^ a)) ^ a) = 0 := by
    rw [← Nat.cast_pow]; exact ZMod.natCast_self (q ^ a)
  ext g
  constructor
  · rintro ⟨A, hA⟩
    rw [MonoidHom.mem_ker]
    ext i j
    have hcoe : ((slReduceLevel q m a ha g : SL(2, ZMod (q^a)))
        : Matrix (Fin 2) (Fin 2) (ZMod (q^a))) i j
        = ZMod.castHom (pow_dvd_pow q ha) (ZMod (q^a))
            ((g : Matrix (Fin 2) (Fin 2) (ZMod (q^m))) i j) := by
      simp only [slReduceLevel, SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Matrix.map_apply]
    rw [hcoe, hA, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul,
      map_pow, map_natCast, hqa0, zero_mul, add_zero,
      show ((1 : SL(2, ZMod (q^a))) : Matrix _ _ _) i j
        = (1 : Matrix (Fin 2) (Fin 2) (ZMod (q^a))) i j from rfl]
    simp only [Matrix.one_apply, apply_ite (ZMod.castHom (pow_dvd_pow q ha) (ZMod (q^a))),
      map_one, map_zero]
  · intro hker

    rw [MonoidHom.mem_ker] at hker
    have hentry : ∀ i j, (q : ZMod (q ^ m)) ^ a ∣
        ((g : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) i j
          - (1 : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) i j) := by
      intro i j
      set x := (g : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) i j
          - (1 : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) i j with hxdef
      have hcast : ZMod.castHom (pow_dvd_pow q ha) (ZMod (q ^ a)) x = 0 := by
        have h1 : ZMod.castHom (pow_dvd_pow q ha) (ZMod (q^a))
            ((g : Matrix (Fin 2) (Fin 2) (ZMod (q^m))) i j)
            = (1 : Matrix (Fin 2) (Fin 2) (ZMod (q^a))) i j := by
          have h0 : ((slReduceLevel q m a ha g : SL(2, ZMod (q^a)))
              : Matrix (Fin 2) (Fin 2) (ZMod (q^a))) i j
              = ((1 : SL(2, ZMod (q^a))) : Matrix _ _ _) i j := by rw [hker]
          simpa only [slReduceLevel, SpecialLinearGroup.map_apply_coe,
            RingHom.mapMatrix_apply, Matrix.map_apply, sl2coe_one] using h0
        rw [hxdef, map_sub, h1]
        simp only [Matrix.one_apply,
          apply_ite (ZMod.castHom (pow_dvd_pow q ha) (ZMod (q^a))), map_one, map_zero,
          sub_self]

      have hrepr : ((x.val : ℕ) : ZMod (q ^ m)) = x := by
        rw [ZMod.natCast_val, ZMod.cast_id]
      rw [← hrepr, map_natCast, ZMod.natCast_eq_zero_iff] at hcast
      obtain ⟨y, hy⟩ := hcast
      exact ⟨(y : ZMod (q ^ m)), by rw [← hrepr, hy, Nat.cast_mul, Nat.cast_pow]⟩
    choose Y hY using hentry
    refine ⟨Matrix.of Y, ?_⟩
    ext i j
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, ← hY,
      add_sub_cancel]

theorem commutator_mem_congFilt_add {a b : ℕ}
    {g h : SL(2, ZMod (q ^ m))} (hg : g ∈ congFilt q m a) (hh : h ∈ congFilt q m b) :
    g * h * g⁻¹ * h⁻¹ ∈ congFilt q m (a + b) := by
  obtain ⟨A, hA⟩ := (mem_congFilt_iff q m).mp hg
  obtain ⟨B, hB⟩ := (mem_congFilt_iff q m).mp hh
  obtain ⟨A', hA'⟩ := (mem_congFilt_iff q m).mp ((congFilt q m a).inv_mem hg)
  obtain ⟨B', hB'⟩ := (mem_congFilt_iff q m).mp ((congFilt q m b).inv_mem hh)
  set x := (q : ZMod (q ^ m)) ^ a with hx
  set y := (q : ZMod (q ^ m)) ^ b with hy

  refine ⟨(A * B - B * A) * (1 + x • A') * (1 + y • B'), ?_⟩
  have hxinv : (1 + x • A) * (1 + x • A') = 1 := by
    rw [← hA, ← hA', ← sl2coe_mul, mul_inv_cancel,
      sl2coe_one]
  have hyinv : (1 + y • B) * (1 + y • B') = 1 := by
    rw [← hB, ← hB', ← sl2coe_mul, mul_inv_cancel,
      sl2coe_one]
  have hcomm : (1 + x • A) * (1 + y • B) - (1 + y • B) * (1 + x • A)
      = (x * y) • (A * B - B * A) := by
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
    module
  have hcomm' : (1 + x • A) * (1 + y • B)
      = (1 + y • B) * (1 + x • A) + (x * y) • (A * B - B * A) :=
    sub_eq_iff_eq_add'.mp hcomm
  calc ((g * h * g⁻¹ * h⁻¹ : SL(2, ZMod (q ^ m))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m)))
      = ((1 + x • A) * (1 + y • B)) * ((1 + x • A') * (1 + y • B')) := by
        simp only [sl2coe_mul, hA, hB, hA', hB', mul_assoc]
    _ = ((1 + y • B) * (1 + x • A) + (x * y) • (A * B - B * A))
          * ((1 + x • A') * (1 + y • B')) := by rw [hcomm']
    _ = (1 + y • B) * ((1 + x • A) * (1 + x • A')) * (1 + y • B')
          + (x * y) • ((A * B - B * A) * ((1 + x • A') * (1 + y • B'))) := by
        rw [add_mul, smul_mul_assoc, mul_assoc, mul_assoc, ← mul_assoc (1 + x • A)]
    _ = 1 + ((q : ZMod (q ^ m)) ^ (a + b))
          • ((A * B - B * A) * (1 + x • A') * (1 + y • B')) := by
        rw [hxinv, mul_one, hyinv, hx, hy, ← pow_add, mul_assoc]

theorem congFilt_commutator_le (a b : ℕ) :
    ⁅congFilt q m a, congFilt q m b⁆ ≤ congFilt q m (a + b) := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  exact commutator_mem_congFilt_add q m hg hh

theorem congFilt_commutative {a : ℕ} (ha : m ≤ a + a) :
    ∀ g ∈ congFilt q m a, ∀ h ∈ congFilt q m a, g * h = h * g := by
  intro g hg h hh
  have hc : g * h * g⁻¹ * h⁻¹ ∈ congFilt q m (a + a) :=
    commutator_mem_congFilt_add q m hg hh
  have h1 : g * h * g⁻¹ * h⁻¹ = 1 :=
    Subgroup.mem_bot.mp ((congFilt_of_self_le q m ha).symm ▸ hc)
  have h2 : g * h = g * h * g⁻¹ * h⁻¹ * (h * g) := by group
  rw [h2, h1, one_mul]

theorem pow_q_of_one_add_smul_sub_two (hq : q.Prime) (hq2 : q ≠ 2) (hm : 3 ≤ m)
    (A : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) :
    (1 + ((q : ZMod (q ^ m)) ^ (m - 2)) • A) ^ q
      = 1 + ((q : ZMod (q ^ m)) ^ (m - 1)) • A :=
  one_add_smul_pow_prime_eq q m hq hq2 hm A

theorem pow_q_mem_congFilt_add_one {a : ℕ} (ha : 1 ≤ a)
    {g : SL(2, ZMod (q ^ m))} (hg : g ∈ congFilt q m a) :
    g ^ q ∈ congFilt q m (a + 1) := by
  obtain ⟨A, hA⟩ := hg
  obtain ⟨B, hB⟩ := one_add_smul_pow q ((q : ZMod (q ^ m)) ^ a) A
  refine ⟨A + ((q : ZMod (q ^ m)) ^ (a - 1)) • B, ?_⟩
  have hcoe : ((g ^ q : SL(2, ZMod (q ^ m))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m)))
      = (1 + ((q : ZMod (q ^ m)) ^ a) • A) ^ q := by
    rw [sl2coe_pow]; rw [hA]
  rw [hcoe, hB, smul_add, smul_smul]
  have h1 : ((q : ℕ) : ZMod (q ^ m)) * (q : ZMod (q ^ m)) ^ a
      = (q : ZMod (q ^ m)) ^ (a + 1) := by rw [← pow_succ']
  have h2 : ((q : ZMod (q ^ m)) ^ a) ^ 2
      = (q : ZMod (q ^ m)) ^ (a + 1) * (q : ZMod (q ^ m)) ^ (a - 1) := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  rw [h1, h2, add_assoc]

theorem congFilt_pow_q_eq_one {g : SL(2, ZMod (q ^ m))} (hm : 2 ≤ m)
    (hg : g ∈ congFilt q m (m - 1)) : g ^ q = 1 := by
  have h := pow_q_mem_congFilt_add_one q m (a := m - 1) (by omega) hg
  rw [Nat.sub_add_cancel (by omega : 1 ≤ m)] at h
  exact Subgroup.mem_bot.mp ((congFilt_of_self_le q m le_rfl).symm ▸ h)

theorem coe_pow_q_of_mem_congFilt_sub_two (hq : q.Prime) (hq2 : q ≠ 2) (hm : 3 ≤ m)
    {l : SL(2, ZMod (q ^ m))} {X : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))}
    (hl : (l : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m)))
        = 1 + ((q : ZMod (q ^ m)) ^ (m - 2)) • X) :
    ((l ^ q : SL(2, ZMod (q ^ m))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m)))
        = 1 + ((q : ZMod (q ^ m)) ^ (m - 1)) • X := by
  rw [sl2coe_pow]
  rw [hl, pow_q_of_one_add_smul_sub_two q m hq hq2 hm]

theorem zmod_dvd_of_pow_mul_eq_zero (hq : q.Prime) (hm : 1 ≤ m) {x : ZMod (q ^ m)}
    (hx : (q : ZMod (q ^ m)) ^ (m - 1) * x = 0) : (q : ZMod (q ^ m)) ∣ x := by
  haveI : NeZero (q ^ m) := ⟨pow_ne_zero m hq.ne_zero⟩
  have hrepr : ((x.val : ℕ) : ZMod (q ^ m)) = x := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  rw [← hrepr, ← Nat.cast_pow, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hx
  set v := x.val with hv
  have hdvd : q ∣ v := by
    have heq : q ^ m = q ^ (m - 1) * q := by rw [← pow_succ, Nat.sub_add_cancel hm]
    rw [heq] at hx
    exact (Nat.mul_dvd_mul_iff_left (pow_pos hq.pos (m - 1))).mp hx
  obtain ⟨y, hy⟩ := hdvd
  exact ⟨(y : ZMod (q ^ m)), by rw [← hrepr, hy, Nat.cast_mul]⟩

theorem congFilt_pow_q_injOn (hq : q.Prime) (hq2 : q ≠ 2) (hm : 3 ≤ m) :
    ∀ l ∈ congFilt q m (m - 2), l ^ q = 1 → l ∈ congFilt q m (m - 1) := by
  rintro l ⟨X, hX⟩ hlq
  have h := coe_pow_q_of_mem_congFilt_sub_two q m hq hq2 hm hX
  rw [hlq] at h
  rw [sl2coe_one] at h
  rw [eq_comm, add_eq_left] at h

  have hdvd : ∀ i j, (q : ZMod (q ^ m)) ∣ X i j := by
    intro i j
    apply zmod_dvd_of_pow_mul_eq_zero q m hq (by omega)
    have hentry := congrArg (fun M => M i j) h
    simpa only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] using hentry
  choose Y hY using hdvd
  refine ⟨Matrix.of Y, ?_⟩
  rw [hX]
  congr 1
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, hY,
    ← mul_assoc, ← pow_succ]
  congr 2
  omega

theorem det_one_add_smul_fin_two {R : Type*} [CommRing R] (c : R)
    (X : Matrix (Fin 2) (Fin 2) R) :
    (1 + c • X).det = 1 + c * Matrix.trace X + c ^ 2 * X.det := by
  rw [Matrix.one_fin_two, Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.empty_val']
  ring

theorem congFilt_exists_pow_q (hq : q.Prime) (hq2 : q ≠ 2) (hm : 3 ≤ m) [NeZero q] :
    ∀ k ∈ congFilt q m (m - 1), ∃ l ∈ congFilt q m (m - 2), l ^ q = k := by
  intro k hk
  rw [mem_congFilt_iff] at hk
  obtain ⟨X, hX⟩ := hk
  haveI : NeZero (q ^ m) := ⟨pow_ne_zero m (NeZero.ne q)⟩
  set qm : ZMod (q ^ m) := (q : ZMod (q ^ m)) with hqm
  have hqm_pow_m : qm ^ m = 0 := by
    simp only [hqm, ← Nat.cast_pow, ZMod.natCast_self]
  have hqm_pow_of_le : ∀ {j : ℕ}, m ≤ j → qm ^ j = 0 := fun {j} hj => by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hj
    rw [hd, pow_add, hqm_pow_m, zero_mul]

  have hdetk := k.det_coe
  rw [hX, det_one_add_smul_fin_two] at hdetk
  have hqm2m2 : (qm ^ (m - 1)) ^ 2 = 0 := by
    rw [← pow_mul]; exact hqm_pow_of_le (by omega)
  rw [hqm2m2, zero_mul, add_zero] at hdetk
  have htr0 : qm ^ (m - 1) * Matrix.trace X = 0 := by linear_combination hdetk

  obtain ⟨t, ht⟩ := zmod_dvd_of_pow_mul_eq_zero q m hq (by omega) htr0

  set a : ZMod (q ^ m) := -t - qm ^ (m - 3) * X.det with ha
  set Y : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m)) := !![a, 0; 0, 0] with hY
  set Z : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m)) := X + qm • Y with hZ

  have hdetl : (1 + qm ^ (m - 2) • Z).det = 1 := by
    rw [det_one_add_smul_fin_two]

    have htrZ : Matrix.trace Z = qm * (t + a) := by
      rw [hZ, Matrix.trace_add, Matrix.trace_smul, hY, Matrix.trace_fin_two_of,
        smul_eq_mul, add_zero, ht, ← hqm]
      ring
    have hdetZ : Z.det = X.det + qm * a * X 1 1 := by
      rw [hZ, Matrix.det_fin_two, Matrix.det_fin_two, hY]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Matrix.empty_val', mul_zero, add_zero]
      ring
    rw [htrZ, hdetZ]

    have heq1 : qm ^ (m - 2) * (qm * (t + a)) = qm ^ (m - 1) * (t + a) := by
      rw [show m - 1 = m - 2 + 1 from by omega, pow_succ]; ring
    have heq2 : (qm ^ (m - 2)) ^ 2 = qm ^ (2 * (m - 2)) := by rw [← pow_mul, mul_comm]
    rw [heq1, heq2]

    have hta : t + a = -(qm ^ (m - 3) * X.det) := by rw [ha]; ring
    rw [hta, mul_neg, ← mul_assoc, ← pow_add]
    have hstep : m - 1 + (m - 3) = 2 * (m - 2) := by omega
    rw [hstep, mul_add, ← add_assoc, neg_add_cancel_right]

    rw [show qm ^ (2 * (m - 2)) * (qm * a * X 1 1)
        = qm ^ (2 * (m - 2) + 1) * (a * X 1 1) from by ring,
      hqm_pow_of_le (by omega), zero_mul, add_zero]

  refine ⟨⟨_, hdetl⟩, (mem_congFilt_iff q m).mpr ⟨Z, rfl⟩, ?_⟩

  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have hlq := coe_pow_q_of_mem_congFilt_sub_two q m hq hq2 hm
    (l := ⟨_, hdetl⟩) (X := Z) rfl
  rw [hlq, hX, hZ, smul_add, smul_smul, ← pow_succ,
    show m - 1 + 1 = m from by omega, hqm_pow_m, zero_smul, add_zero]

theorem slReduceLevel_surjective [NeZero q] {a : ℕ} (ha : a ≤ m) :
    Function.Surjective (slReduceLevel q m a ha) := by
  intro g
  haveI : NeZero (q ^ a) := ⟨pow_ne_zero a (NeZero.ne q)⟩
  haveI : NeZero (q ^ m) := ⟨pow_ne_zero m (NeZero.ne q)⟩

  obtain ⟨g', hg'⟩ := SL2_reduction_surjective (q ^ a) g
  refine ⟨SpecialLinearGroup.map (Int.castRingHom (ZMod (q ^ m))) g', ?_⟩
  rw [← hg']
  ext i j
  simp only [slReduceLevel, SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply]
  exact map_intCast _ _

noncomputable def congFiltQuotientEquiv (hm : 1 ≤ m) [NeZero q] :
    SL(2, ZMod (q ^ m)) ⧸ congFilt q m (m - 1) ≃* SL(2, ZMod (q ^ (m - 1))) :=
  (QuotientGroup.quotientMulEquivOfEq
    (congFilt_eq_ker_reduceLevel q m (a := m - 1) (by omega))).trans
  (QuotientGroup.quotientKerEquivOfSurjective _
    (slReduceLevel_surjective q m (by omega)))

end
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

end Ihara
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

end Inl_P2B_Filtration
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

section Inl_P2B_M2WAbelian

namespace Ihara
p2m_export "Ihara" "HasTrivialSchurMultiplier hasTrivialSchurMultiplier_of_subsingleton exists_pow_prime_pow_eq_one_of_sl2_stem"
p2m_open "Ihara"

p2m_open "Matrix SpecialLinearGroup Matrix.SpecialLinearGroup"

open scoped MatrixGroups commutatorElement

variable (q : ℕ)

private theorem sl2coe_mul' {R : Type*} [CommRing R] (A B : SL(2, R)) :
    ((A * B : SL(2, R)) : Matrix (Fin 2) (Fin 2) R)
      = (A : Matrix (Fin 2) (Fin 2) R) * B := rfl
private theorem sl2coe_mk' {R : Type*} [CommRing R]
    (A : Matrix (Fin 2) (Fin 2) R) (h : A.det = 1) :
    ((⟨A, h⟩ : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = A := rfl

section Elements

variable [NeZero q]

abbrev kE : SL(2, ZMod (q ^ 2)) := uElt (q : ZMod (q ^ 2))

abbrev kF : SL(2, ZMod (q ^ 2)) := vElt (q : ZMod (q ^ 2))

def kH : SL(2, ZMod (q ^ 2)) :=
  ⟨!![1 + (q : ZMod (q^2)), 0; 0, 1 - (q : ZMod (q^2))], by
    rw [Matrix.det_fin_two_of]; ring_nf
    rw [show ((q : ZMod (q^2))^2 : ZMod (q^2)) = 0 from by
      rw [← Nat.cast_pow]; exact ZMod.natCast_self (q ^ 2)]; ring⟩

def weyl2 : SL(2, ZMod (q ^ 2)) :=
  ⟨!![0, -1; 1, 0], by rw [Matrix.det_fin_two_of]; ring⟩

omit [NeZero q] in
private theorem q_sq_eq_zero : ((q : ZMod (q ^ 2)) ^ 2 : ZMod (q ^ 2)) = 0 := by
  rw [← Nat.cast_pow]; exact ZMod.natCast_self (q ^ 2)

omit [NeZero q] in
theorem kE_coe : ((kE q : SL(2, ZMod (q^2))) : Matrix (Fin 2) (Fin 2) (ZMod (q^2)))
    = !![1, (q : ZMod (q^2)); 0, 1] := rfl

omit [NeZero q] in
theorem kF_coe : ((kF q : SL(2, ZMod (q^2))) : Matrix (Fin 2) (Fin 2) (ZMod (q^2)))
    = !![1, 0; (q : ZMod (q^2)), 1] := rfl

omit [NeZero q] in
theorem kH_coe : ((kH q : SL(2, ZMod (q^2))) : Matrix (Fin 2) (Fin 2) (ZMod (q^2)))
    = !![1 + (q : ZMod (q^2)), 0; 0, 1 - (q : ZMod (q^2))] := rfl

omit [NeZero q] in
theorem kE_mem : kE q ∈ congFilt q 2 1 :=
  (mem_congFilt_iff q 2).mpr ⟨!![0, 1; 0, 0], by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [kE, uElt, pow_one, Matrix.one_fin_two]⟩

omit [NeZero q] in
theorem kF_mem : kF q ∈ congFilt q 2 1 :=
  (mem_congFilt_iff q 2).mpr ⟨!![0, 0; 1, 0], by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [kF, vElt, pow_one, Matrix.one_fin_two]⟩

omit [NeZero q] in
theorem kH_mem : kH q ∈ congFilt q 2 1 :=
  (mem_congFilt_iff q 2).mpr ⟨!![1, 0; 0, -1], by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [kH_coe, pow_one, Matrix.one_fin_two, sub_eq_add_neg]⟩

omit [NeZero q] in

theorem kE_pow_q : (kE q) ^ q = 1 :=
  congFilt_pow_q_eq_one q 2 (by omega) (kE_mem q)

omit [NeZero q] in

theorem one_add_q_smul_pow {g : SL(2, ZMod (q ^ 2))}
    {X : Matrix (Fin 2) (Fin 2) (ZMod (q ^ 2))}
    (hg : (g : Matrix (Fin 2) (Fin 2) (ZMod (q ^ 2))) = 1 + (q : ZMod (q ^ 2)) • X)
    (n : ℕ) :
    ((g ^ n : SL(2, ZMod (q ^ 2))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ 2)))
      = 1 + ((n * q : ℕ) : ZMod (q ^ 2)) • X := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [_root_.pow_succ g k, sl2coe_mul', ih, hg]
    have hkq : ((k * q : ℕ) : ZMod (q^2)) • X * ((q : ZMod (q^2)) • X) = 0 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Nat.cast_mul, mul_assoc,
        ← sq, q_sq_eq_zero q, mul_zero, zero_smul]
    rw [add_mul, one_mul, mul_add, mul_one, hkq, add_zero, add_assoc, ← add_smul]
    congr 2
    push_cast; ring

variable {q}

omit [NeZero q] in

theorem uElt_pow {R : Type*} [CommRing R] (b : R) (n : ℕ) :
    (uElt b) ^ n = uElt ((n : R) * b) := by
  induction n with
  | zero =>
    apply Matrix.SpecialLinearGroup.ext; intro i j
    simp [uElt, Matrix.one_fin_two]
  | succ k ih =>
    rw [_root_.pow_succ, ih, ← uElt_add, Nat.cast_succ, add_mul, one_mul]

omit [NeZero q] in

theorem vElt_pow {R : Type*} [CommRing R] (c : R) (n : ℕ) :
    (vElt c) ^ n = vElt ((n : R) * c) := by
  induction n with
  | zero =>
    apply Matrix.SpecialLinearGroup.ext; intro i j
    simp [vElt, Matrix.one_fin_two]
  | succ k ih =>
    rw [_root_.pow_succ, ih]
    apply Matrix.SpecialLinearGroup.ext; intro i j
    simp only [vElt, sl2coe_mul', sl2coe_mk',
      Nat.cast_succ]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    all_goals ring

omit [NeZero q] in

theorem hElt_inv_mul_kH_mul_hElt (t : (ZMod (q^2))ˣ) :
    (hElt t)⁻¹ * kH q * hElt t = kH q := by
  have hinv : (hElt t)⁻¹ = hElt t⁻¹ := by
    apply Matrix.SpecialLinearGroup.ext; intro i j
    rw [SL2_inv_expl]; fin_cases i <;> (fin_cases j <;> simp [hElt])
  have htt : (t : ZMod (q^2)) * ↑t⁻¹ = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have htt' : (↑t⁻¹ : ZMod (q^2)) * ↑t = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  apply Matrix.SpecialLinearGroup.ext; intro i j
  rw [hinv]
  simp only [sl2coe_mul', hElt_coe, kH_coe, inv_inv]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals
    first
    | linear_combination (q : ZMod (q^2)) * htt + htt
    | linear_combination - (q : ZMod (q^2)) * htt' + htt'

omit [NeZero q] in
theorem weyl2_inv :
    (weyl2 q)⁻¹ = ⟨!![(0 : ZMod (q^2)), 1; -1, 0], by rw [Matrix.det_fin_two_of]; ring⟩ := by
  apply Matrix.SpecialLinearGroup.ext; intro i j
  rw [SL2_inv_expl]
  fin_cases i <;> fin_cases j <;> simp [weyl2]

omit [NeZero q] in
theorem kH_inv_coe :
    (((kH q)⁻¹ : SL(2, ZMod (q^2))) : Matrix (Fin 2) (Fin 2) (ZMod (q^2)))
      = !![1 - (q : ZMod (q^2)), 0; 0, 1 + (q : ZMod (q^2))] := by
  rw [SL2_inv_expl]
  ext i j; fin_cases i <;> fin_cases j <;> simp [kH]

omit [NeZero q] in

theorem weyl2_conj_kE :
    weyl2 q * kE q * (weyl2 q)⁻¹ = (kF q)⁻¹ := by
  apply Matrix.SpecialLinearGroup.ext; intro i j
  rw [weyl2_inv, SL2_inv_expl]
  simp only [sl2coe_mul', kE_coe, kF_coe, weyl2]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [NeZero q] in

theorem weyl2_conj_kF :
    weyl2 q * kF q * (weyl2 q)⁻¹ = (kE q)⁻¹ := by
  apply Matrix.SpecialLinearGroup.ext; intro i j
  rw [weyl2_inv, SL2_inv_expl]
  simp only [sl2coe_mul', kE_coe, kF_coe, weyl2]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [NeZero q] in

theorem weyl2_conj_kH :
    weyl2 q * kH q * (weyl2 q)⁻¹ = (kH q)⁻¹ := by
  apply Matrix.SpecialLinearGroup.ext; intro i j
  rw [weyl2_inv, kH_inv_coe]
  simp only [sl2coe_mul', kH_coe, weyl2]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

variable (q)

omit [NeZero q] in

theorem one_add_q_smul_mul {A B : Matrix (Fin 2) (Fin 2) (ZMod (q^2))} :
    (1 + (q : ZMod (q^2)) • A) * (1 + (q : ZMod (q^2)) • B)
      = 1 + (q : ZMod (q^2)) • (A + B) := by
  rw [mul_add, mul_one, add_mul, one_mul, smul_add, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, ← sq, q_sq_eq_zero q, zero_smul, add_zero, add_assoc]

omit [NeZero q] in
private theorem kE_coe' : ((kE q : SL(2, ZMod (q^2))) : Matrix (Fin 2) (Fin 2) (ZMod (q^2)))
    = 1 + (q : ZMod (q^2)) • !![(0 : ZMod (q^2)), 1; 0, 0] := by
  rw [kE_coe, Matrix.one_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

omit [NeZero q] in
private theorem kF_coe' : ((kF q : SL(2, ZMod (q^2))) : Matrix (Fin 2) (Fin 2) (ZMod (q^2)))
    = 1 + (q : ZMod (q^2)) • !![(0 : ZMod (q^2)), 0; 1, 0] := by
  rw [kF_coe, Matrix.one_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

omit [NeZero q] in
private theorem kH_coe' : ((kH q : SL(2, ZMod (q^2))) : Matrix (Fin 2) (Fin 2) (ZMod (q^2)))
    = 1 + (q : ZMod (q^2)) • !![(1 : ZMod (q^2)), 0; 0, -1] := by
  rw [kH_coe, Matrix.one_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp [sub_eq_add_neg]

theorem congFilt_one_eq_closure_efh :
    congFilt q 2 1 = Subgroup.closure {kE q, kF q, kH q} := by
  haveI : NeZero (q ^ 2) := ⟨pow_ne_zero 2 (NeZero.ne q)⟩
  refine le_antisymm ?_ ?_
  · intro g hg
    rw [mem_congFilt_iff] at hg
    obtain ⟨X, hX⟩ := hg
    rw [pow_one] at hX

    have hdet := g.det_coe
    rw [hX, det_one_add_smul_fin_two, q_sq_eq_zero q, zero_mul, add_zero] at hdet
    have htr : (q : ZMod (q^2)) * (X 0 0 + X 1 1) = 0 := by
      rw [← Matrix.trace_fin_two]; linear_combination hdet

    have heq : g = (kH q) ^ (X 0 0).val * (kE q) ^ (X 0 1).val * (kF q) ^ (X 1 0).val := by
      apply Matrix.SpecialLinearGroup.ext; intro i j
      rw [sl2coe_mul', sl2coe_mul',
        one_add_q_smul_pow q (kH_coe' q) _, one_add_q_smul_pow q (kE_coe' q) _,
        one_add_q_smul_pow q (kF_coe' q) _, hX,
        show ((X 0 0).val * q : ℕ) = ((X 0 0).val : ℕ) * q from rfl,
        Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, mul_smul, mul_smul, mul_smul,
        smul_comm ((X 0 0).val : ZMod (q^2)) (q : ZMod (q^2)),
        smul_comm ((X 0 1).val : ZMod (q^2)) (q : ZMod (q^2)),
        smul_comm ((X 1 0).val : ZMod (q^2)) (q : ZMod (q^2)),
        one_add_q_smul_mul, one_add_q_smul_mul]
      have hval : ∀ z : ZMod (q^2), ((z.val : ℕ) : ZMod (q^2)) = z := fun z => by
        rw [ZMod.natCast_val, ZMod.cast_id]

      rw [Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
        smul_eq_mul, smul_eq_mul]
      congr 1
      fin_cases i <;> fin_cases j <;> simp [hval]

      linear_combination htr
    rw [heq]
    exact mul_mem (mul_mem
      (pow_mem (Subgroup.subset_closure (by simp)) _)
      (pow_mem (Subgroup.subset_closure (by simp)) _))
      (pow_mem (Subgroup.subset_closure (by simp)) _)
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact kE_mem q
    · exact kF_mem q
    · exact kH_mem q

end Elements
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

section AbstractEngine

variable {E : Type*} [Group E]

theorem commutatorElement_mul_central_left {a b c : E} (hc : c ∈ Subgroup.center E) :
    ⁅a * c, b⁆ = ⁅a, b⁆ := by
  have h1 : b * c = c * b := Subgroup.mem_center_iff.mp hc b
  simp only [commutatorElement_def, _root_.mul_inv_rev]
  rw [show a * c * b * (c⁻¹ * a⁻¹) * b⁻¹ = a * (c * b * c⁻¹) * a⁻¹ * b⁻¹ from by group,
    ← h1, mul_assoc b, mul_inv_cancel, mul_one]

theorem commutatorElement_mul_left_of_central {a b c : E}
    (hbc : ⁅b, c⁆ ∈ Subgroup.center E) : ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have h1 : a * ⁅b, c⁆ = ⁅b, c⁆ * a := Subgroup.mem_center_iff.mp hbc a
  have h2 : ⁅a, c⁆ * ⁅b, c⁆ = ⁅b, c⁆ * ⁅a, c⁆ := Subgroup.mem_center_iff.mp hbc ⁅a, c⁆
  rw [show a * ⁅b, c⁆ * a⁻¹ = ⁅b, c⁆ from by rw [h1, mul_assoc, mul_inv_cancel, mul_one], h2]

theorem commutatorElement_conj_of_central {a b g : E}
    (hab : ⁅a, b⁆ ∈ Subgroup.center E) : ⁅g * a * g⁻¹, g * b * g⁻¹⁆ = ⁅a, b⁆ := by
  rw [← conjugate_commutatorElement]
  have h1 : g * ⁅a, b⁆ = ⁅a, b⁆ * g := Subgroup.mem_center_iff.mp hab g
  rw [h1, mul_assoc, mul_inv_cancel, mul_one]

theorem commutatorElement_mul_central_right {a b c : E} (hc : c ∈ Subgroup.center E) :
    ⁅a, b * c⁆ = ⁅a, b⁆ := by
  rw [← commutatorElement_inv (g₁ := b * c), commutatorElement_mul_central_left hc,
    commutatorElement_inv]

theorem commutatorElement_mul_right_of_central {a b c : E}
    (hac : ⁅a, c⁆ ∈ Subgroup.center E) : ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  have hca : ⁅c, a⁆ ∈ Subgroup.center E := by rw [← commutatorElement_inv]; exact inv_mem hac
  rw [← commutatorElement_inv (g₁ := b * c), commutatorElement_mul_left_of_central hca,
    _root_.mul_inv_rev, commutatorElement_inv, commutatorElement_inv,
    (Subgroup.mem_center_iff.mp hac ⁅a, b⁆)]

theorem commutatorElement_inv_left_of_central {a b : E}
    (hab : ⁅a, b⁆ ∈ Subgroup.center E) : ⁅a⁻¹, b⁆ = ⁅a, b⁆⁻¹ := by
  have h : ⁅a⁻¹ * a, b⁆ = ⁅a⁻¹, b⁆ * ⁅a, b⁆ := commutatorElement_mul_left_of_central hab
  rw [inv_mul_cancel, commutatorElement_one_left] at h
  exact (eq_inv_of_mul_eq_one_left h.symm)

theorem commutatorElement_inv_right_of_central {a b : E}
    (hab : ⁅a, b⁆ ∈ Subgroup.center E) : ⁅a, b⁻¹⁆ = ⁅a, b⁆⁻¹ := by
  have hba : ⁅b, a⁆ ∈ Subgroup.center E := by rw [← commutatorElement_inv]; exact inv_mem hab
  rw [← commutatorElement_inv (g₁ := b⁻¹), commutatorElement_inv_left_of_central hba,
    commutatorElement_inv]

theorem commutatorElement_pow_left_of_central {a b : E} (n : ℕ)
    (hab : ⁅a, b⁆ ∈ Subgroup.center E) : ⁅a ^ n, b⁆ = ⁅a, b⁆ ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [_root_.pow_succ, commutatorElement_mul_left_of_central hab, ih, _root_.pow_succ]

end AbstractEngine
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

variable {E : Type} [Group E]

theorem uElt_one_mul_kF_mul_uElt_neg_one :
    uElt (1 : ZMod (q ^ 2)) * kF q * uElt (-1) = kF q * kH q * uElt (-(q : ZMod (q ^ 2))) := by
  have hq2 : ((q : ZMod (q ^ 2)) ^ 2 : ZMod (q ^ 2)) = 0 := q_sq_eq_zero q
  have hq3 : ((q : ZMod (q ^ 2)) ^ 3 : ZMod (q ^ 2)) = 0 := by
    have h : ((q : ZMod (q ^ 2)) ^ 3 : ZMod (q ^ 2)) = (q : ZMod (q ^ 2)) ^ 2 * q := by ring
    rw [h, hq2, zero_mul]
  apply Matrix.SpecialLinearGroup.ext; intro i j
  rw [sl2coe_mul', sl2coe_mul', sl2coe_mul', sl2coe_mul', kF_coe, kH_coe, uElt_coe, uElt_coe,
    uElt_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    (try ring_nf) <;> (try simp [hq2, hq3])

theorem comap_congFilt_one_commute (π : E →* SL(2, ZMod (q ^ 2)))
    (hsurj : Function.Surjective π) (hcen : MonoidHom.ker π ≤ Subgroup.center E)
    (hq : q.Prime) (hq2 : q ≠ 2) [NeZero q] :
    ∀ x ∈ (congFilt q 2 1).comap π, ∀ y ∈ (congFilt q 2 1).comap π, Commute x y := by

  set K := congFilt q 2 1 with hKdef
  set W := K.comap π with hW
  have hKW : ∀ a ∈ K, ∃ x ∈ W, π x = a := fun a ha => by
    obtain ⟨x, hx⟩ := hsurj a; exact ⟨x, by simp [hW, Subgroup.mem_comap, hx, ha], hx⟩
  have hβcen : ∀ x ∈ W, ∀ y ∈ W, ⁅x, y⁆ ∈ Subgroup.center E := fun x hx y hy => by
    apply hcen
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact (congFilt_commutative q 2 (by omega) (π x) hx (π y) hy)
  have hliftL : ∀ x ∈ W, ∀ x' ∈ W, π x = π x' → ∀ y ∈ W, ⁅x, y⁆ = ⁅x', y⁆ := by
    intro x hx x' hx' hxx' y hy
    have hc : x'⁻¹ * x ∈ Subgroup.center E := hcen (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxx', inv_mul_cancel])
    rw [show x = x' * (x'⁻¹ * x) from by group, commutatorElement_mul_central_left hc]
  have hliftR : ∀ x ∈ W, ∀ y ∈ W, ∀ y' ∈ W, π y = π y' → ⁅x, y⁆ = ⁅x, y'⁆ := by
    intro x hx y hy y' hy' hyy'
    rw [← commutatorElement_inv (g₁ := y), hliftL y hy y' hy' hyy' x hx,
      commutatorElement_inv]

  obtain ⟨eE, heEW, heE⟩ := hKW (kE q) (hKdef ▸ kE_mem q)
  obtain ⟨fE, hfEW, hfE⟩ := hKW (kF q) (hKdef ▸ kF_mem q)
  obtain ⟨hE, hhEW, hhE⟩ := hKW (kH q) (hKdef ▸ kH_mem q)

  have hβq : ∀ x ∈ W, ∀ y ∈ W, ⁅x, y⁆ ^ q = 1 := by
    intro x hx y hy
    rw [← commutatorElement_pow_left_of_central q (hβcen x hx y hy)]
    have hxq : x ^ q ∈ Subgroup.center E := hcen (by
      rw [MonoidHom.mem_ker, map_pow]
      exact congFilt_pow_q_eq_one q 2 (by omega) (Subgroup.mem_comap.mp hx))
    exact commutatorElement_eq_one_iff_commute.mpr
      ((Subgroup.mem_center_iff.mp hxq y).symm)
  have heq1 : ∀ {x : E} {m : ℕ}, Nat.Coprime m q → x ^ m = 1 → x ^ q = 1 → x = 1 := by
    intro x m hco hm hn
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hm) (orderOf_dvd_of_pow_eq_one hn)
    rw [hco] at hd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  have hconj : ∀ (g : SL(2, ZMod (q^2))) {x y x' y' : E}, x ∈ W → y ∈ W →
      x' ∈ W → y' ∈ W → π x' = g * π x * g⁻¹ → π y' = g * π y * g⁻¹ →
      ⁅x', y'⁆ = ⁅x, y⁆ := by
    intro g x y x' y' hx hy hx' hy' hxx' hyy'
    obtain ⟨gE, hgE⟩ := hsurj g
    have hgxW : gE * x * gE⁻¹ ∈ W := Subgroup.mem_comap.mpr (by
      rw [map_mul, map_mul, map_inv, hgE, ← hxx']; exact Subgroup.mem_comap.mp hx')
    have hgyW : gE * y * gE⁻¹ ∈ W := Subgroup.mem_comap.mpr (by
      rw [map_mul, map_mul, map_inv, hgE, ← hyy']; exact Subgroup.mem_comap.mp hy')
    rw [hliftL x' hx' (gE * x * gE⁻¹) hgxW
        (by rw [map_mul, map_mul, map_inv, hgE, hxx']) y' hy',
      hliftR (gE * x * gE⁻¹) hgxW y' hy' (gE * y * gE⁻¹) hgyW
        (by rw [map_mul, map_mul, map_inv, hgE, hyy']),
      commutatorElement_conj_of_central (hβcen x hx y hy)]

  have huinv : (uElt (1 : ZMod (q ^ 2)))⁻¹ = uElt (-1) :=
    inv_eq_of_mul_eq_one_right (by rw [← uElt_add, add_neg_cancel, uElt_zero])
  have hkEinv : (kE q)⁻¹ = uElt (-(q : ZMod (q ^ 2))) :=
    inv_eq_of_mul_eq_one_right (by rw [kE, ← uElt_add, add_neg_cancel, uElt_zero])
  have hEH : ⁅eE, hE⁆ = 1 := by
    have hy'W : fE * hE * eE⁻¹ ∈ W := W.mul_mem (W.mul_mem hfEW hhEW) (W.inv_mem heEW)
    have hc : ⁅eE, fE * hE * eE⁻¹⁆ = ⁅eE, fE⁆ := by
      refine hconj (uElt 1) heEW hfEW heEW hy'W ?_ ?_
      · rw [heE, show uElt (1 : ZMod (q ^ 2)) * kE q = kE q * uElt 1 from by
          rw [kE, ← uElt_add, ← uElt_add, add_comm], mul_inv_cancel_right]
      · rw [map_mul, map_mul, map_inv, hfE, hhE, heE, huinv, hkEinv]
        exact (uElt_one_mul_kF_mul_uElt_neg_one q).symm
    rw [commutatorElement_mul_right_of_central (hβcen eE heEW eE⁻¹ (W.inv_mem heEW)),
      commutatorElement_mul_right_of_central (hβcen eE heEW hE hhEW),
      show ⁅eE, eE⁻¹⁆ = 1 from by rw [commutatorElement_def]; group, mul_one] at hc
    exact mul_left_cancel (a := ⁅eE, fE⁆) (by rw [mul_one]; exact hc)

  have hFH : ⁅fE, hE⁆ = 1 := by
    have hwconj : ⁅fE⁻¹, hE⁻¹⁆ = ⁅eE, hE⁆ := by
      refine hconj (weyl2 q) heEW hhEW (W.inv_mem hfEW) (W.inv_mem hhEW) ?_ ?_
      · rw [map_inv, hfE, heE]; exact weyl2_conj_kE.symm
      · rw [map_inv, hhE]; exact weyl2_conj_kH.symm
    rw [commutatorElement_inv_left_of_central (hβcen fE hfEW _ (W.inv_mem hhEW)),
      commutatorElement_inv_right_of_central (hβcen fE hfEW hE hhEW)] at hwconj
    rw [inv_inv] at hwconj
    rw [hwconj, hEH]

  have hEF : ⁅eE, fE⁆ = 1 := by
    refine heq1 (m := 2) ((Nat.coprime_primes Nat.prime_two hq).mpr (by omega))
      ?_ (hβq eE heEW fE hfEW)
    have hwconj : ⁅fE⁻¹, eE⁻¹⁆ = ⁅eE, fE⁆ := by
      refine hconj (weyl2 q) heEW hfEW (W.inv_mem hfEW) (W.inv_mem heEW) ?_ ?_
      · rw [map_inv, hfE, heE]; exact weyl2_conj_kE.symm
      · rw [map_inv, heE, hfE]; exact weyl2_conj_kF.symm
    rw [commutatorElement_inv_left_of_central (hβcen fE hfEW _ (W.inv_mem heEW)),
      commutatorElement_inv_right_of_central (hβcen fE hfEW eE heEW),
      inv_inv, ← commutatorElement_inv] at hwconj
    rw [sq]; nth_rw 1 [← hwconj]; exact inv_mul_cancel _

  have hgen : ∀ a ∈ ({kE q, kF q, kH q} : Set _), ∀ b ∈ ({kE q, kF q, kH q} : Set _),
      ∀ x ∈ W, π x = a → ∀ y ∈ W, π y = b → ⁅x, y⁆ = 1 := by
    intro a ha b hb x hx hxa y hy hyb

    have hsw : ∀ {s : E} {g : SL(2, ZMod (q^2))}, s ∈ W → π s = g →
        ∀ {z : E}, z ∈ W → π z = g → ∀ {w : E}, w ∈ W → ⁅s, w⁆ = ⁅z, w⁆ := by
      intro s g hs hsg z hz hzg w hw
      exact hliftL s hs z hz (hsg.trans hzg.symm) w hw
    have hswR : ∀ {z : E}, z ∈ W → ∀ {s : E} {g : SL(2, ZMod (q^2))}, s ∈ W → π s = g →
        ∀ {w : E}, w ∈ W → π w = g → ⁅z, s⁆ = ⁅z, w⁆ := by
      intro z hz s g hs hsg w hw hwg
      exact hliftR z hz s hs w hw (hsg.trans hwg.symm)
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      [(rw [hsw hx hxa heEW heE hy, hswR heEW hy hyb heEW heE]; simp);
       (rw [hsw hx hxa heEW heE hy, hswR heEW hy hyb hfEW hfE]; exact hEF);
       (rw [hsw hx hxa heEW heE hy, hswR heEW hy hyb hhEW hhE]; exact hEH);
       (rw [hsw hx hxa hfEW hfE hy, hswR hfEW hy hyb heEW heE];
         rw [← _root_.inv_inj, ← commutatorElement_inv] at hEF; simpa using hEF);
       (rw [hsw hx hxa hfEW hfE hy, hswR hfEW hy hyb hfEW hfE]; simp);
       (rw [hsw hx hxa hfEW hfE hy, hswR hfEW hy hyb hhEW hhE]; exact hFH);
       (rw [hsw hx hxa hhEW hhE hy, hswR hhEW hy hyb heEW heE];
         rw [← _root_.inv_inj, ← commutatorElement_inv] at hEH; simpa using hEH);
       (rw [hsw hx hxa hhEW hhE hy, hswR hhEW hy hyb hfEW hfE];
         rw [← _root_.inv_inj, ← commutatorElement_inv] at hFH; simpa using hFH);
       (rw [hsw hx hxa hhEW hhE hy, hswR hhEW hy hyb hhEW hhE]; simp)]

  have hK : K = Subgroup.closure {kE q, kF q, kH q} := hKdef ▸ congFilt_one_eq_closure_efh q
  intro x hx y hy
  rw [show (Commute x y ↔ ⁅x, y⁆ = 1) from commutatorElement_eq_one_iff_commute.symm]
  have hxK : π x ∈ Subgroup.closure {kE q, kF q, kH q} := hK ▸ hx
  have hyK : π y ∈ Subgroup.closure {kE q, kF q, kH q} := hK ▸ hy

  let P : (a b : SL(2, ZMod (q^2))) →
      a ∈ Subgroup.closure {kE q, kF q, kH q} →
      b ∈ Subgroup.closure {kE q, kF q, kH q} → Prop :=
    fun a b _ _ => ∀ x ∈ W, π x = a → ∀ y ∈ W, π y = b → ⁅x, y⁆ = 1
  suffices h : P (π x) (π y) hxK hyK from h x hx rfl y hy rfl
  refine Subgroup.closure_induction₂ (p := P) (fun a b ha hb => hgen a ha b hb)
    ?_ ?_ ?_ ?_ ?_ ?_ hxK hyK
  ·
    intro b _ x' hx' hx1 y' hy' _
    exact (commutatorElement_eq_one_iff_commute.mpr
      ((Subgroup.mem_center_iff.mp (hcen (π.mem_ker.mpr hx1)) y').symm))
  ·
    intro a _ x' _ _ y' _ hy1
    exact (commutatorElement_eq_one_iff_commute.mpr
      (Subgroup.mem_center_iff.mp (hcen (π.mem_ker.mpr hy1)) x'))
  ·
    intro a b c ha hb hc Pac Pbc x' hx' hxab y' hy' hyc
    obtain ⟨xa, hxaW, hxa⟩ := hKW a (hK ▸ ha)
    obtain ⟨xb, hxbW, hxb⟩ := hKW b (hK ▸ hb)
    rw [hliftL x' hx' (xa * xb) (W.mul_mem hxaW hxbW)
        (by rw [map_mul, hxa, hxb, hxab]) y' hy',
      commutatorElement_mul_left_of_central (hβcen xb hxbW y' hy'),
      Pac xa hxaW hxa y' hy' hyc, Pbc xb hxbW hxb y' hy' hyc, one_mul]
  ·
    intro b c a hb hc ha Pab Pac x' hx' hxa y' hy' hybc
    obtain ⟨yb, hybW, hyb⟩ := hKW b (hK ▸ hb)
    obtain ⟨yc, hycW, hyc⟩ := hKW c (hK ▸ hc)
    rw [hliftR x' hx' y' hy' (yb * yc) (W.mul_mem hybW hycW)
        (by rw [map_mul, hyb, hyc, hybc]),
      commutatorElement_mul_right_of_central (hβcen x' hx' yc hycW),
      Pab x' hx' hxa yb hybW hyb, Pac x' hx' hxa yc hycW hyc, one_mul]
  ·
    intro a b ha hb Pab x' hx' hxa y' hy' hyb
    obtain ⟨xa, hxaW, hxaE⟩ := hKW a (hK ▸ ha)
    rw [hliftL x' hx' xa⁻¹ (W.inv_mem hxaW)
        (by rw [map_inv, hxaE, hxa]) y' hy',
      commutatorElement_inv_left_of_central (hβcen xa hxaW y' hy'),
      Pab xa hxaW hxaE y' hy' hyb, inv_one]
  ·
    intro a b ha hb Pab x' hx' hxa y' hy' hyb
    obtain ⟨yb', hybW, hybE⟩ := hKW b (hK ▸ hb)
    rw [hliftR x' hx' y' hy' yb'⁻¹ (W.inv_mem hybW)
        (by rw [map_inv, hybE, hyb]),
      commutatorElement_inv_right_of_central (hβcen x' hx' yb' hybW),
      Pab x' hx' hxa yb' hybW hybE, inv_one]

end Ihara
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

end Inl_P2B_M2WAbelian
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

section Inl_P2B_StemDescent

namespace Ihara
p2m_export "Ihara" "HasTrivialSchurMultiplier hasTrivialSchurMultiplier_of_subsingleton exists_pow_prime_pow_eq_one_of_sl2_stem"
p2m_open "Ihara"

open Subgroup

open scoped commutatorElement

section PowerIdentities

variable {E : Type*} [Group E]

theorem mul_pow_eq_of_commutator_comm {a b z : E} (hza : z * a = a * z) (hzb : z * b = b * z)
    (hab : b * a = z * a * b) (n : ℕ) : (a * b) ^ n = z ^ n.choose 2 * a ^ n * b ^ n := by
  have hpow : ∀ n : ℕ, b ^ n * a = z ^ n * a * b ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hzbn : z ^ n * b = b * z ^ n := ((show Commute z b from hzb).pow_left n).eq
      calc b ^ (n + 1) * a = b * (b ^ n * a) := by rw [pow_succ']; group
        _ = b * (z ^ n * a * b ^ n) := by rw [ih]
        _ = (b * z ^ n) * a * b ^ n := by group
        _ = (z ^ n * b) * a * b ^ n := by rw [hzbn]
        _ = z ^ n * (b * a) * b ^ n := by group
        _ = z ^ n * (z * a * b) * b ^ n := by rw [hab]
        _ = z ^ (n + 1) * a * b ^ (n + 1) := by rw [pow_succ, pow_succ]; group
  induction n with
  | zero => simp
  | succ n ih =>
    have hzan : z ^ n * a ^ n = a ^ n * z ^ n :=
      ((show Commute z a from hza).pow_left n).pow_right n |>.eq
    calc (a * b) ^ (n + 1) = (a * b) ^ n * (a * b) := pow_succ _ _
      _ = z ^ n.choose 2 * a ^ n * (b ^ n * a) * b := by rw [ih]; group
      _ = z ^ n.choose 2 * a ^ n * (z ^ n * a * b ^ n) * b := by rw [hpow]
      _ = z ^ n.choose 2 * (a ^ n * z ^ n) * a * b ^ n * b := by group
      _ = z ^ n.choose 2 * (z ^ n * a ^ n) * a * b ^ n * b := by rw [hzan]
      _ = z ^ (n.choose 2 + n) * a ^ (n + 1) * b ^ (n + 1) := by
        rw [pow_add, pow_succ, pow_succ]; group
      _ = z ^ (n + 1).choose 2 * a ^ (n + 1) * b ^ (n + 1) := by
        have hc : (n + 1).choose 2 = n.choose 2 + n := by
          have := Nat.choose_succ_succ' n 1
          simpa [Nat.choose_one_right, add_comm] using this
        rw [hc]

theorem pow_mul_mul_pow_inv_eq_of_comm {a b z : E} (hza : z * a = a * z)
    (hab : a * b * a⁻¹ = z * b) (n : ℕ) : a ^ n * b * (a ^ n)⁻¹ = z ^ n * b := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hzan : a * z ^ n = z ^ n * a := ((show Commute z a from hza).pow_left n).eq.symm
    calc a ^ (n + 1) * b * (a ^ (n + 1))⁻¹ = a * (a ^ n * b * (a ^ n)⁻¹) * a⁻¹ := by
          rw [pow_succ']; group
      _ = a * (z ^ n * b) * a⁻¹ := by rw [ih]
      _ = (a * z ^ n) * b * a⁻¹ := by group
      _ = z ^ n * (a * b * a⁻¹) := by rw [hzan]; group
      _ = z ^ (n + 1) * b := by rw [hab, pow_succ]; group

theorem pow_choose_two_eq_one_of_odd {z : E} {q : ℕ} (hq : Odd q) (hz : z ^ q = 1) :
    z ^ q.choose 2 = 1 := by
  obtain ⟨k, rfl⟩ := hq
  have h : (2 * k + 1).choose 2 = (2 * k + 1) * k := by
    rw [Nat.choose_two_right, show 2 * k + 1 - 1 = 2 * k by omega,
      show (2 * k + 1) * (2 * k) = 2 * ((2 * k + 1) * k) by ring, Nat.mul_div_cancel_left _ two_pos]
  rw [h, pow_mul, hz, one_pow]

end PowerIdentities
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

section StemDescent

universe u

variable {E G : Type u} [Group E] [Group G]

theorem comap_le_commutator_of_stem (π : E →* G) (hπ : Function.Surjective π)
    (hcomm : π.ker ≤ commutator E) (K : Subgroup G) [K.Normal]
    (hK : K ≤ commutator G) (hQ : HasTrivialSchurMultiplier (G ⧸ K)) :
    K.comap π ≤ ⁅(⊤ : Subgroup E), K.comap π⁆ := by
  haveI hWn : (K.comap π).Normal := inferInstance
  set W := K.comap π with hW
  haveI hDn : (⁅(⊤ : Subgroup E), W⁆).Normal := inferInstance
  set D := ⁅(⊤ : Subgroup E), W⁆ with hD

  let ρ : E →* G ⧸ K := (QuotientGroup.mk' K).comp π
  have hρ : ∀ x : E, ρ x = 1 ↔ x ∈ W := fun x => by
    simp only [ρ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hW,
      mem_comap]
  have hDle : D ≤ ρ.ker := fun x hx => by
    rw [MonoidHom.mem_ker, hρ]
    exact commutator_le_right (H₁ := ⊤) (H₂ := W) hx
  let ρ' : E ⧸ D →* G ⧸ K := QuotientGroup.lift D ρ hDle
  have hρ' : ∀ x : E, ρ' (x : E ⧸ D) = 1 ↔ x ∈ W := fun x => by
    simp only [ρ', QuotientGroup.lift_mk]
    exact hρ x
  have hsurj : Function.Surjective ρ' := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨e, rfl⟩ := hπ g
    exact ⟨(e : E ⧸ D), by simp only [ρ', QuotientGroup.lift_mk]; rfl⟩

  have hcent' : ρ'.ker ≤ center (E ⧸ D) := by
    intro x hx
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rw [MonoidHom.mem_ker, hρ'] at hx
    rw [mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    have h1 : ((⁅y, x⁆ : E) : E ⧸ D) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (commutator_mem_commutator (mem_top y) hx)
    have h2 := map_commutatorElement (QuotientGroup.mk' D) y x
    simp only [QuotientGroup.mk'_apply] at h2
    rw [h2, commutatorElement_eq_one_iff_commute] at h1
    exact h1.eq

  have hmapE : (commutator E).map π = commutator G := by
    rw [_root_.commutator_def, _root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hπ]
  have hWcomm : W ≤ commutator E := by
    intro x hx
    have hπx : π x ∈ (commutator E).map π := by rw [hmapE]; exact hK hx
    obtain ⟨y, hy, hyx⟩ := hπx
    have hyx' : y⁻¹ * x ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
    rw [show x = y * (y⁻¹ * x) by group]
    exact mul_mem hy (hcomm hyx')
  have hcomm' : ρ'.ker ≤ commutator (E ⧸ D) := by
    intro x hx
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rw [MonoidHom.mem_ker, hρ'] at hx
    have hmapD : (commutator E).map (QuotientGroup.mk' D) = commutator (E ⧸ D) := by
      rw [_root_.commutator_def, _root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective D)]
    rw [← hmapD]
    exact ⟨x, hWcomm hx, rfl⟩

  have htriv := hQ (E ⧸ D) ρ' hsurj hcent' hcomm'
  intro x hx
  have hx' : (x : E ⧸ D) ∈ ρ'.ker := by rw [MonoidHom.mem_ker, hρ']; exact hx
  rw [htriv, mem_bot, QuotientGroup.eq_one_iff] at hx'
  exact hx'

theorem pow_eq_one_of_stem (π : E →* G) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ center E) (hcomm : π.ker ≤ commutator E) (K : Subgroup G) [K.Normal]
    (hK : K ≤ commutator G) (hQ : HasTrivialSchurMultiplier (G ⧸ K))
    (hKab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) {q : ℕ} (hq : Odd q) (hKq : ∀ k ∈ K, k ^ q = 1) :
    ∀ w ∈ K.comap π, w ^ q = 1 := by
  haveI hWn : (K.comap π).Normal := inferInstance
  set W := K.comap π with hW
  have hcenK : ∀ z ∈ π.ker, ∀ e : E, z * e = e * z := fun z hz e =>
    ((mem_center_iff.mp (hcen hz)) e).symm

  have hWq : ∀ w ∈ W, w ^ q ∈ π.ker := fun w hw => by
    rw [MonoidHom.mem_ker, map_pow]
    exact hKq _ hw

  have hWW : ∀ w ∈ W, ∀ w' ∈ W, ⁅w, w'⁆ ∈ π.ker := fun w hw w' hw' => by
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact hKab _ hw _ hw'
  have hWWq : ∀ w ∈ W, ∀ w' ∈ W, ⁅w, w'⁆ ^ q = 1 := fun w hw w' hw' => by
    set z := ⁅w, w'⁆ with hz
    have hcz := hcenK z (hWW w hw w' hw')
    have h1 : w * w' * w⁻¹ = z * w' := by rw [hz, commutatorElement_def]; group
    have h2 := pow_mul_mul_pow_inv_eq_of_comm (hcz w) h1 q

    rw [hcenK _ (hWq w hw) w', mul_inv_cancel_right] at h2
    have h3 : z ^ q * w' = 1 * w' := by rw [one_mul]; exact h2.symm
    exact mul_right_cancel h3

  have hmul : ∀ x ∈ W, ∀ y ∈ W, (x * y) ^ q = x ^ q * y ^ q := fun x hx y hy => by
    set z := ⁅y, x⁆ with hz
    have hcz := hcenK z (hWW y hy x hx)
    have hyx : y * x = z * x * y := by rw [hz, commutatorElement_def]; group
    rw [mul_pow_eq_of_commutator_comm (hcz x) (hcz y) hyx q,
      pow_choose_two_eq_one_of_odd hq (hWWq y hy x hx), one_mul]

  let T : Subgroup E :=
    { carrier := {x | x ∈ W ∧ x ^ q = 1}
      mul_mem' := by
        rintro x y ⟨hx, hxq⟩ ⟨hy, hyq⟩
        exact ⟨mul_mem hx hy, by rw [hmul x hx y hy, hxq, hyq, one_mul]⟩
      one_mem' := ⟨one_mem _, one_pow _⟩
      inv_mem' := by
        rintro x ⟨hx, hxq⟩
        exact ⟨inv_mem hx, by rw [inv_pow, hxq, inv_one]⟩ }
  have hT : ⁅(⊤ : Subgroup E), W⁆ ≤ T := by
    rw [commutator_le]
    intro e _ w hw
    have hew : e * w * e⁻¹ ∈ W := (inferInstance : W.Normal).conj_mem w hw e
    refine ⟨commutator_le_right (H₁ := ⊤) (H₂ := W) (commutator_mem_commutator (mem_top e) hw), ?_⟩
    calc ⁅e, w⁆ ^ q = ((e * w * e⁻¹) * w⁻¹) ^ q := by rw [commutatorElement_def]
      _ = (e * w * e⁻¹) ^ q * w⁻¹ ^ q := hmul _ hew _ (inv_mem hw)
      _ = e * w ^ q * e⁻¹ * w⁻¹ ^ q := by rw [conj_pow]
      _ = 1 := by rw [← hcenK _ (hWq w hw) e, inv_pow]; group
  intro w hw
  exact (hT (comap_le_commutator_of_stem π hπ hcomm K hK hQ hw)).2

theorem ker_pow_eq_one_of_stem (π : E →* G) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ center E) (hcomm : π.ker ≤ commutator E) (K : Subgroup G) [K.Normal]
    (hK : K ≤ commutator G) (hQ : HasTrivialSchurMultiplier (G ⧸ K))
    (hKab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) {q : ℕ} (hq : Odd q) (hKq : ∀ k ∈ K, k ^ q = 1) :
    ∀ c ∈ π.ker, c ^ q = 1 := fun c hc =>
  pow_eq_one_of_stem π hπ hcen hcomm K hK hQ hKab hq hKq c
    (by rw [mem_comap, MonoidHom.mem_ker.mp hc]; exact one_mem K)

theorem ker_eq_bot_of_stem_of_layer (π : E →* G) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ center E) (hcomm : π.ker ≤ commutator E) (K L : Subgroup G) [K.Normal]
    [L.Normal] (hK : K ≤ commutator G) (hQ : HasTrivialSchurMultiplier (G ⧸ K)) {q : ℕ}
    (hq : Odd q) (hKq : ∀ k ∈ K, k ^ q = 1) (hKL : K ≤ L)
    (hLK : ∀ l ∈ L, ∀ k ∈ K, l * k = k * l) (hLL : ⁅L, L⁆ ≤ K)
    (hroot : ∀ k ∈ K, ∃ l ∈ L, l ^ q = k) (hinj : ∀ l ∈ L, l ^ q = 1 → l ∈ K) : π.ker = ⊥ := by
  haveI hWn : (K.comap π).Normal := inferInstance
  haveI hUn : (L.comap π).Normal := inferInstance
  set W := K.comap π with hW
  set U := L.comap π with hU
  have hKab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x := fun x hx y hy => hLK x (hKL hx) y hy
  have hcenK : ∀ z ∈ π.ker, ∀ e : E, z * e = e * z := fun z hz e =>
    ((mem_center_iff.mp (hcen hz)) e).symm
  have hCW : π.ker ≤ W := fun c hc => by
    rw [hW, mem_comap, MonoidHom.mem_ker.mp hc]; exact one_mem K
  have hWU : W ≤ U := comap_mono hKL
  have hWq := pow_eq_one_of_stem π hπ hcen hcomm K hK hQ hKab hq hKq

  have hdec : ∀ w ∈ W, ∃ h ∈ U, ∃ c ∈ π.ker, w = h ^ q * c := fun w hw => by
    obtain ⟨l, hl, hlq⟩ := hroot (π w) hw
    obtain ⟨h, rfl⟩ := hπ l
    refine ⟨h, mem_comap.mpr hl, (h ^ q)⁻¹ * w, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hlq, inv_mul_cancel]

  have hUW : ∀ u ∈ U, ∀ w ∈ W, u * w = w * u := by
    intro u hu w hw
    obtain ⟨h, hh, c, hc, rfl⟩ := hdec w hw

    set v := ⁅u, h⁆ with hv
    have hvW : v ∈ W := by
      rw [hW, mem_comap, hv, map_commutatorElement]
      exact hLL (commutator_mem_commutator hu hh)
    set z := ⁅h, v⁆ with hz
    have hzC : z ∈ π.ker := by
      rw [MonoidHom.mem_ker, hz, map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact hLK _ hh _ hvW
    have hcz := hcenK z hzC

    have h1 : u * h * u⁻¹ = v * h := by rw [hv, commutatorElement_def]; group
    have h2 : h * v = z * v * h := by rw [hz, commutatorElement_def]; group
    have h3 : u * h ^ q * u⁻¹ = h ^ q := by
      rw [← conj_pow, h1, mul_pow_eq_of_commutator_comm (hcz v) (hcz h) h2 q,
        pow_choose_two_eq_one_of_odd hq (hWq z (hCW hzC)), hWq v hvW]
      group
    calc u * (h ^ q * c) = (u * h ^ q * u⁻¹) * u * c := by group
      _ = h ^ q * (u * c) := by rw [h3]; group
      _ = h ^ q * c * u := by rw [← hcenK c hc u]; group

  have hθ : ∀ x ∈ U, ∀ y ∈ U, (x * y) ^ q = x ^ q * y ^ q := fun x hx y hy => by
    set z := ⁅y, x⁆ with hz
    have hzW : z ∈ W := by
      rw [hW, mem_comap, hz, map_commutatorElement]
      exact hLL (commutator_mem_commutator hy hx)
    have hyx : y * x = z * x * y := by rw [hz, commutatorElement_def]; group
    rw [mul_pow_eq_of_commutator_comm (hUW x hx z hzW).symm (hUW y hy z hzW).symm hyx q,
      pow_choose_two_eq_one_of_odd hq (hWq z hzW), one_mul]

  let Θ : Subgroup E :=
    { carrier := {x | ∃ h ∈ U, h ^ q = x}
      mul_mem' := by
        rintro x y ⟨h₁, hh₁, rfl⟩ ⟨h₂, hh₂, rfl⟩
        exact ⟨h₁ * h₂, mul_mem hh₁ hh₂, hθ _ hh₁ _ hh₂⟩
      one_mem' := ⟨1, one_mem _, one_pow _⟩
      inv_mem' := by
        rintro x ⟨h, hh, rfl⟩
        exact ⟨h⁻¹, inv_mem hh, inv_pow _ _⟩ }

  have hΘ : ⁅(⊤ : Subgroup E), W⁆ ≤ Θ := by
    rw [commutator_le]
    intro e _ w hw
    obtain ⟨h, hh, c, hc, rfl⟩ := hdec w hw
    have heh : e * h * e⁻¹ ∈ U := (inferInstance : U.Normal).conj_mem h hh e
    refine ⟨e * h * e⁻¹ * h⁻¹, mul_mem heh (inv_mem hh), ?_⟩
    rw [hθ _ heh _ (inv_mem hh), conj_pow, inv_pow, commutatorElement_def]
    calc e * h ^ q * e⁻¹ * (h ^ q)⁻¹ = e * h ^ q * (e⁻¹ * c * c⁻¹) * (h ^ q)⁻¹ := by group
      _ = e * h ^ q * (c * e⁻¹ * c⁻¹) * (h ^ q)⁻¹ := by rw [← hcenK c hc e⁻¹]
      _ = e * (h ^ q * c) * e⁻¹ * (h ^ q * c)⁻¹ := by group

  have hΘC : ∀ x ∈ Θ, x ∈ π.ker → x = 1 := by
    rintro x ⟨h, hh, rfl⟩ hx
    have hπh : π h ∈ K := hinj (π h) hh (by rw [← map_pow]; exact MonoidHom.mem_ker.mp hx)
    exact hWq h hπh

  rw [eq_bot_iff]
  intro c hc
  rw [mem_bot]
  exact hΘC c (hΘ (comap_le_commutator_of_stem π hπ hcomm K hK hQ (hCW hc))) hc

end StemDescent
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

end Ihara
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

end Inl_P2B_StemDescent
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

section Inl_L32_TopLayer

set_option autoImplicit false

namespace Ihara
p2m_export "Ihara" "HasTrivialSchurMultiplier hasTrivialSchurMultiplier_of_subsingleton exists_pow_prime_pow_eq_one_of_sl2_stem"
p2m_open "Ihara"

open Matrix
open scoped MatrixGroups commutatorElement

namespace TopLayer

private theorem sl2coe_mul_L {R : Type*} [CommRing R] (A B : SL(2, R)) :
    ((A * B : SL(2, R)) : Matrix (Fin 2) (Fin 2) R)
      = (A : Matrix (Fin 2) (Fin 2) R) * B := rfl

variable (q m : ℕ)

def sL : ZMod (q ^ m) := (q : ZMod (q ^ m)) ^ (m - 1)

variable {q m}

theorem q_pow_m_eq_zero : ((q : ZMod (q ^ m)) ^ m) = 0 := by
  have : ((q ^ m : ℕ) : ZMod (q ^ m)) = 0 := ZMod.natCast_self (q ^ m)
  rwa [Nat.cast_pow] at this

theorem sL_mul_q (hm : 1 ≤ m) : sL q m * (q : ZMod (q ^ m)) = 0 := by
  rw [sL, ← pow_succ, Nat.sub_add_cancel hm, q_pow_m_eq_zero]

theorem sL_mul_sL (hm : 2 ≤ m) : sL q m * sL q m = 0 := by
  rw [sL, ← pow_add, show m - 1 + (m - 1) = m + (m - 2) by omega, pow_add, q_pow_m_eq_zero,
    zero_mul]

variable (q m)

def layMat (a b c : ZMod (q ^ m)) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m)) :=
  !![1 + sL q m * b, sL q m * a; sL q m * c, 1 - sL q m * b]

variable {q m}

theorem det_layMat (hm : 2 ≤ m) (a b c : ZMod (q ^ m)) : (layMat q m a b c).det = 1 := by
  have hs := sL_mul_sL (q := q) hm
  rw [layMat, Matrix.det_fin_two_of]
  linear_combination (-(b * b) - a * c) * hs

variable (q m)

def lay (hm : 2 ≤ m) (a b c : ZMod (q ^ m)) : SL(2, ZMod (q ^ m)) :=
  ⟨layMat q m a b c, det_layMat hm a b c⟩

variable {q m}

theorem lay_coe (hm : 2 ≤ m) (a b c : ZMod (q ^ m)) :
    ((lay q m hm a b c : SL(2, ZMod (q ^ m))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m)))
      = !![1 + sL q m * b, sL q m * a; sL q m * c, 1 - sL q m * b] := rfl

theorem lay_congr (hm : 2 ≤ m) {a b c a' b' c' : ZMod (q ^ m)}
    (ha : sL q m * a = sL q m * a') (hb : sL q m * b = sL q m * b')
    (hc : sL q m * c = sL q m * c') : lay q m hm a b c = lay q m hm a' b' c' := by
  apply Matrix.SpecialLinearGroup.ext; intro i j
  change (lay q m hm a b c : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) i j
    = (lay q m hm a' b' c' : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) i j
  rw [lay_coe, lay_coe, ha, hb, hc]

theorem lay_mul (hm : 2 ≤ m) (a b c a' b' c' : ZMod (q ^ m)) :
    lay q m hm a b c * lay q m hm a' b' c' = lay q m hm (a + a') (b + b') (c + c') := by
  have hs := sL_mul_sL (q := q) hm
  apply Matrix.SpecialLinearGroup.ext; intro i j
  change ((lay q m hm a b c * lay q m hm a' b' c' : SL(2, ZMod (q ^ m)))
      : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) i j
    = (lay q m hm (a + a') (b + b') (c + c') : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) i j
  rw [sl2coe_mul_L, lay_coe, lay_coe, lay_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (b * b' + a * c') * hs
  · linear_combination (b * a' - a * b') * hs
  · linear_combination (c * b' - b * c') * hs
  · linear_combination (c * a' + b * b') * hs

theorem lay_zero (hm : 2 ≤ m) : lay q m hm 0 0 0 = 1 := by
  apply Matrix.SpecialLinearGroup.ext; intro i j
  change (lay q m hm 0 0 0 : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) i j
    = ((1 : SL(2, ZMod (q ^ m))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) i j
  rw [lay_coe, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp

theorem lay_pow (hm : 2 ≤ m) (a b c : ZMod (q ^ m)) (n : ℕ) :
    lay q m hm a b c ^ n = lay q m hm ((n : ZMod (q ^ m)) * a) (n * b) (n * c) := by
  induction n with
  | zero => rw [pow_zero, ← lay_zero hm]; simp
  | succ n ih =>
    rw [pow_succ, ih, lay_mul]
    push_cast
    congr 1 <;> ring

theorem exists_lay_of_mem_top (hm : 2 ≤ m) {g : SL(2, ZMod (q ^ m))}
    (hg : g ∈ congFilt q m (m - 1)) : ∃ a b c, g = lay q m hm a b c := by
  obtain ⟨X, hX⟩ := (mem_congFilt_iff q m).mp hg
  have hs := sL_mul_sL (q := q) hm
  have hX' : (g : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) = 1 + sL q m • X := hX

  have hdet := g.det_coe
  rw [hX', det_one_add_smul_fin_two, Matrix.trace_fin_two, sq, hs, zero_mul, add_zero] at hdet
  have htr : sL q m * (X 0 0 + X 1 1) = 0 := by linear_combination hdet
  refine ⟨X 0 1, X 0 0, X 1 0, ?_⟩
  apply Matrix.SpecialLinearGroup.ext; intro i j
  change (g : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) i j
    = (lay q m hm (X 0 1) (X 0 0) (X 1 0) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) i j
  rw [hX', lay_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_fin_two]
  linear_combination htr

theorem u_mul_lay (hm : 2 ≤ m) :
    uElt (1 : ZMod (q ^ m)) * lay q m hm 0 0 1 = lay q m hm (-1) 1 1 * uElt 1 := by
  apply Matrix.SpecialLinearGroup.ext; intro i j
  change ((uElt (1 : ZMod (q ^ m)) * lay q m hm 0 0 1 : SL(2, ZMod (q ^ m)))
      : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) i j
    = ((lay q m hm (-1) 1 1 * uElt 1 : SL(2, ZMod (q ^ m))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) i j
  rw [sl2coe_mul_L, sl2coe_mul_L, lay_coe, lay_coe, uElt_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem u_mul_layH (hm : 2 ≤ m) :
    uElt (1 : ZMod (q ^ m)) * lay q m hm 0 1 0 = lay q m hm (-2) 1 0 * uElt 1 := by
  apply Matrix.SpecialLinearGroup.ext; intro i j
  change ((uElt (1 : ZMod (q ^ m)) * lay q m hm 0 1 0 : SL(2, ZMod (q ^ m)))
      : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) i j
    = ((lay q m hm (-2) 1 0 * uElt 1 : SL(2, ZMod (q ^ m))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) i j
  rw [sl2coe_mul_L, sl2coe_mul_L, lay_coe, lay_coe, uElt_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem v_mul_layE (hm : 2 ≤ m) :
    vElt (1 : ZMod (q ^ m)) * lay q m hm 1 0 0 = lay q m hm 1 (-1) (-1) * vElt 1 := by
  apply Matrix.SpecialLinearGroup.ext; intro i j
  change ((vElt (1 : ZMod (q ^ m)) * lay q m hm 1 0 0 : SL(2, ZMod (q ^ m)))
      : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) i j
    = ((lay q m hm 1 (-1) (-1) * vElt 1 : SL(2, ZMod (q ^ m))) : Matrix (Fin 2) (Fin 2) (ZMod (q ^ m))) i j
  rw [sl2coe_mul_L, sl2coe_mul_L, lay_coe, lay_coe, vElt_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem commutatorElement_eq_of_mul_eq {G : Type*} [Group G] {x y z : G}
    (h : x * y = z * y * x) : ⁅x, y⁆ = z := by
  rw [commutatorElement_def, h]; group

theorem comm_u_F (hm : 2 ≤ m) :
    ⁅uElt (1 : ZMod (q ^ m)), lay q m hm 0 0 1⁆ = lay q m hm (-1) 1 0 :=
  commutatorElement_eq_of_mul_eq (by
    rw [u_mul_lay hm, lay_mul]; congr 3 <;> ring)

theorem comm_u_H (hm : 2 ≤ m) :
    ⁅uElt (1 : ZMod (q ^ m)), lay q m hm 0 1 0⁆ = lay q m hm (-2) 0 0 :=
  commutatorElement_eq_of_mul_eq (by
    rw [u_mul_layH hm, lay_mul]; congr 3 <;> ring)

theorem comm_v_E (hm : 2 ≤ m) :
    ⁅vElt (1 : ZMod (q ^ m)), lay q m hm 1 0 0⁆ = lay q m hm 0 (-1) (-1) :=
  commutatorElement_eq_of_mul_eq (by
    rw [v_mul_layE hm, lay_mul]; congr 3 <;> ring)

end TopLayer
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

open TopLayer in

theorem congFilt_top_le_commutator (q m : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hm : 2 ≤ m) :
    congFilt q m (m - 1) ≤ commutator SL(2, ZMod (q ^ m)) := by
  haveI : NeZero (q ^ m) := ⟨pow_ne_zero m hq.ne_zero⟩
  set C := commutator SL(2, ZMod (q ^ m)) with hC
  have hcomm : ∀ x y : SL(2, ZMod (q ^ m)), ⁅x, y⁆ ∈ C := fun x y =>
    Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
  have hsq := sL_mul_q (q := q) (m := m) (by omega)

  have hE2 : lay q m hm (-2) 0 0 ∈ C := comm_u_H hm ▸ hcomm _ _
  have hE : lay q m hm 1 0 0 ∈ C := by
    obtain ⟨k, hk⟩ := hq.odd_of_ne_two hq2
    have hkq : (q : ZMod (q ^ m)) = ((2 * k + 1 : ℕ) : ZMod (q ^ m)) := congrArg Nat.cast hk
    push_cast at hkq
    have h := C.pow_mem hE2 k
    rw [lay_pow] at h
    convert h using 1
    apply lay_congr hm
    · linear_combination hsq - sL q m * hkq
    · simp
    · simp

  have hH : lay q m hm 0 1 0 ∈ C := by
    have h := C.mul_mem (comm_u_F hm ▸ hcomm (uElt 1) (lay q m hm 0 0 1)) hE
    rw [lay_mul] at h
    convert h using 1; apply lay_congr hm <;> ring

  have hFinv : lay q m hm 0 0 (-1) ∈ C := by
    have h := C.mul_mem (comm_v_E hm ▸ hcomm (vElt 1) (lay q m hm 1 0 0)) hH
    rw [lay_mul] at h
    convert h using 1; apply lay_congr hm <;> ring
  have hF : lay q m hm 0 0 1 ∈ C := by
    have hinv : lay q m hm 0 0 1 = (lay q m hm 0 0 (-1))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [lay_mul, ← lay_zero hm]; apply lay_congr hm <;> ring
    rw [hinv]; exact C.inv_mem hFinv

  have hlay : ∀ a b c : ZMod (q ^ m), lay q m hm a b c ∈ C := by
    intro a b c
    have hEa : lay q m hm a 0 0 ∈ C := by
      have h := C.pow_mem hE a.val
      rw [lay_pow, ZMod.natCast_zmod_val] at h
      convert h using 1; apply lay_congr hm <;> ring
    have hHb : lay q m hm 0 b 0 ∈ C := by
      have h := C.pow_mem hH b.val
      rw [lay_pow, ZMod.natCast_zmod_val] at h
      convert h using 1; apply lay_congr hm <;> ring
    have hFc : lay q m hm 0 0 c ∈ C := by
      have h := C.pow_mem hF c.val
      rw [lay_pow, ZMod.natCast_zmod_val] at h
      convert h using 1; apply lay_congr hm <;> ring
    have h := C.mul_mem (C.mul_mem hEa hHb) hFc
    rw [lay_mul, lay_mul] at h
    convert h using 1; apply lay_congr hm <;> ring
  intro g hg
  obtain ⟨a, b, c, rfl⟩ := exists_lay_of_mem_top hm hg
  exact hlay a b c

end Ihara
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

end Inl_L32_TopLayer
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

section Inl_P2B_StepSL

set_option autoImplicit false

namespace Ihara
p2m_export "Ihara" "HasTrivialSchurMultiplier hasTrivialSchurMultiplier_of_subsingleton exists_pow_prime_pow_eq_one_of_sl2_stem"
p2m_open "Ihara"

open Matrix
open scoped MatrixGroups

theorem hasTrivialSchurMultiplier_SL2_ZMod_step (q m : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (hm : 3 ≤ m)
    (IH : HasTrivialSchurMultiplier SL(2, ZMod (q ^ (m - 1)))) :
    HasTrivialSchurMultiplier SL(2, ZMod (q ^ m)) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  intro E _ π hπ hcen hcomm
  have hQ : HasTrivialSchurMultiplier (SL(2, ZMod (q ^ m)) ⧸ congFilt q m (m - 1)) :=
    IH.of_mulEquiv (congFiltQuotientEquiv q m (by omega))
  have hbot : congFilt q m (m - 2 + (m - 1)) = ⊥ := congFilt_of_self_le q m (by omega)
  have hK : congFilt q m (m - 1) ≤ commutator SL(2, ZMod (q ^ m)) :=
    congFilt_top_le_commutator q m hq hq2 (by omega)
  refine ker_eq_bot_of_stem_of_layer π hπ hcen hcomm (congFilt q m (m - 1))
    (congFilt q m (m - 2)) hK hQ (hq.odd_of_ne_two hq2)
    (fun k hk => congFilt_pow_q_eq_one q m (by omega) hk) (congFilt_antitone q m (by omega))
    (fun l hl k hk => ?_) ?_ (congFilt_exists_pow_q q m hq hq2 hm)
    (congFilt_pow_q_injOn q m hq hq2 hm)
  ·
    have hc : l * k * l⁻¹ * k⁻¹ ∈ congFilt q m (m - 2 + (m - 1)) :=
      commutator_mem_congFilt_add q m hl hk
    rw [hbot, Subgroup.mem_bot] at hc
    calc l * k = l * k * l⁻¹ * k⁻¹ * (k * l) := by group
      _ = k * l := by rw [hc, one_mul]
  ·
    exact (congFilt_commutator_le q m (m - 2) (m - 2)).trans (congFilt_antitone q m (by omega))

end Ihara
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

end Inl_P2B_StepSL
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

section Inl_P2A_SL2Card

namespace Ihara
p2m_export "Ihara" "HasTrivialSchurMultiplier hasTrivialSchurMultiplier_of_subsingleton exists_pow_prime_pow_eq_one_of_sl2_stem"
p2m_open "Ihara"

open Matrix

open scoped MatrixGroups

variable (F : Type*) [Field F]

private lemma det_GL_two_surjective :
    Function.Surjective (GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ) := by
  intro u
  have hmul : ∀ x y : F, !![x, 0; 0, 1] * !![y, 0; 0, 1] = !![x * y, 0; 0, 1] := by
    intro x y
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hone : (1 : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  refine ⟨⟨!![(u : F), 0; 0, 1], !![((u⁻¹ : Fˣ) : F), 0; 0, 1], ?_, ?_⟩, ?_⟩
  · rw [hmul, hone]
    norm_num
  · rw [hmul, hone]
    norm_num
  · apply Units.ext
    rw [GeneralLinearGroup.val_det_apply]
    show Matrix.det !![(u : F), 0; 0, 1] = (u : F)
    rw [Matrix.det_fin_two_of]
    ring

private lemma card_ker_det_GL_two :
    Nat.card (MonoidHom.ker (GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ)) =
      Nat.card (SpecialLinearGroup (Fin 2) F) := by
  refine (Nat.card_eq_of_bijective
    (fun g : SpecialLinearGroup (Fin 2) F =>
      (⟨SpecialLinearGroup.toGL g, by
        rw [MonoidHom.mem_ker]
        exact SpecialLinearGroup.coeToGL_det g⟩ :
        MonoidHom.ker (GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ)))
    ⟨?_, ?_⟩).symm
  · intro g g' hgg'
    exact SpecialLinearGroup.toGL_injective (Subtype.ext_iff.mp hgg')
  · rintro ⟨A, hA⟩
    rw [MonoidHom.mem_ker] at hA
    have hAdet : (A : Matrix (Fin 2) (Fin 2) F).det = 1 := by
      have := congrArg (Units.val) hA
      rwa [GeneralLinearGroup.val_det_apply, Units.val_one] at this
    refine ⟨⟨(A : Matrix (Fin 2) (Fin 2) F), hAdet⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rfl

theorem card_SL2_zmod (p : ℕ) [Fact p.Prime] :
    Nat.card (SpecialLinearGroup (Fin 2) (ZMod p)) = p * (p ^ 2 - 1) := by
  have hp : p.Prime := Fact.out
  have key : Nat.card (GL (Fin 2) (ZMod p)) =
      (p - 1) * Nat.card (SpecialLinearGroup (Fin 2) (ZMod p)) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (MonoidHom.ker (GeneralLinearGroup.det : GL (Fin 2) (ZMod p) →* (ZMod p)ˣ))]
    rw [card_ker_det_GL_two]
    congr 1
    rw [Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective _ (det_GL_two_surjective (ZMod p))).toEquiv]
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_two] at key
  norm_num at key
  have h1 : 1 ≤ p := hp.one_lt.le
  have h2 : p ≤ p ^ 2 := by nlinarith
  have h3 : 1 ≤ p ^ 2 := h1.trans h2
  have harith : (p ^ 2 - 1) * (p ^ 2 - p) = (p - 1) * (p * (p ^ 2 - 1)) := by
    zify [h1, h2, h3]
    ring
  rw [harith] at key
  rw [Nat.card_eq_fintype_card]
  exact Nat.eq_of_mul_eq_mul_left (Nat.sub_pos_of_lt hp.one_lt) key.symm

end Ihara
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

end Inl_P2A_SL2Card
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

section Inl_P2B_Induction

set_option autoImplicit false

namespace Ihara
p2m_export "Ihara" "HasTrivialSchurMultiplier hasTrivialSchurMultiplier_of_subsingleton exists_pow_prime_pow_eq_one_of_sl2_stem"
p2m_open "Ihara"

open Matrix
open scoped MatrixGroups

section LevelOne

variable (q : ℕ)

def unipU : SL(2, ZMod q) :=
  ⟨!![1, 1; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

theorem unipU_pow_coe (n : ℕ) :
    ((unipU q ^ n : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q))
      = !![1, (n : ZMod q); 0, 1] := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.cast_zero]
    exact Matrix.one_fin_two
  | succ n ih =>
    rw [pow_succ]
    change ((unipU q ^ n : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) * !![1, 1; 0, 1] = _
    rw [ih, Matrix.mul_fin_two, Nat.cast_succ]
    simp [add_comm]

theorem unipU_pow_self [Fact q.Prime] : unipU q ^ q = 1 :=
  Subtype.ext <| by
    rw [unipU_pow_coe, ZMod.natCast_self]
    exact Matrix.one_fin_two.symm

theorem unipU_ne_one [Fact q.Prime] : unipU q ≠ 1 := by
  intro h
  have h01 := congrArg (fun g : SL(2, ZMod q) => (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1) h
  change (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1
    = (1 : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1 at h01
  simp at h01

theorem orderOf_unipU [Fact q.Prime] : orderOf (unipU q) = q :=
  orderOf_eq_prime (unipU_pow_self q) (unipU_ne_one q)

theorem index_zpowers_unipU [Fact q.Prime] :
    (Subgroup.zpowers (unipU q)).index = q ^ 2 - 1 := by
  have hq : 0 < q := (Fact.out : q.Prime).pos
  have h := (Subgroup.zpowers (unipU q)).card_mul_index
  rw [Nat.card_zpowers, orderOf_unipU, card_SL2_zmod q] at h
  exact Nat.eq_of_mul_eq_mul_left hq h

theorem hasTrivialSchurMultiplier_SL2_ZMod_of_kerPowQ (hq : q.Prime)
    (hA : ∀ (E : Type) [Group E] (π : E →* SL(2, ZMod q)), Function.Surjective π →
      π.ker ≤ Subgroup.center E → ∀ x ∈ π.ker, x ∈ commutator E →
        ∃ k : ℕ, x ^ (q ^ k) = 1) :
    HasTrivialSchurMultiplier SL(2, ZMod q) := by
  haveI : Fact q.Prime := ⟨hq⟩
  intro E _ π hπ hcen hcomm
  refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
  have hxcomm : x ∈ commutator E := hcomm hx
  obtain ⟨k, hk⟩ := hA E π hπ hcen x hx hxcomm
  have htr : x ^ (q ^ 2 - 1) = 1 :=
    index_zpowers_unipU q ▸
      pow_index_eq_one_of_isCyclic_of_stem π hπ hcen (Subgroup.zpowers (unipU q)) hx hxcomm
  have hcop : Nat.Coprime (q ^ k) (q ^ 2 - 1) := by
    refine Nat.Coprime.pow_left k ?_
    have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq.pos
    have h2 : Nat.Coprime (q ^ 2) (q ^ 2 - 1) :=
      (Nat.coprime_self_sub_right h1).mpr (Nat.coprime_one_right _)
    exact (Nat.coprime_pow_left_iff two_pos q (q ^ 2 - 1)).mp h2
  have h : x ^ (q ^ k).gcd (q ^ 2 - 1) = 1 := pow_gcd_eq_one.mpr ⟨hk, htr⟩
  rwa [hcop.gcd_eq_one, pow_one] at h

end LevelOne
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

theorem hasTrivialSchurMultiplier_SL2_ZMod_prime_pow_of (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (hA : ∀ (E : Type) [Group E] (π : E →* SL(2, ZMod q)), Function.Surjective π →
      π.ker ≤ Subgroup.center E → ∀ x ∈ π.ker, x ∈ commutator E →
        ∃ k : ℕ, x ^ (q ^ k) = 1)
    (hM2 : HasTrivialSchurMultiplier SL(2, ZMod (q ^ 2)))
    {n : ℕ} (hn : n ≠ 0) : HasTrivialSchurMultiplier SL(2, ZMod (q ^ n)) := by
  refine Nat.le_induction (m := 1)
    (P := fun n _ => HasTrivialSchurMultiplier SL(2, ZMod (q ^ n))) ?_ ?_ n
    (Nat.one_le_iff_ne_zero.mpr hn)
  · show HasTrivialSchurMultiplier SL(2, ZMod (q ^ 1))
    rw [pow_one]
    exact hasTrivialSchurMultiplier_SL2_ZMod_of_kerPowQ q hq hA
  · intro n hmn ih
    have ih' : HasTrivialSchurMultiplier SL(2, ZMod (q ^ n)) := ih
    show HasTrivialSchurMultiplier SL(2, ZMod (q ^ (n + 1)))
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · obtain rfl : n = 1 := by omega
      exact hM2
    · exact hasTrivialSchurMultiplier_SL2_ZMod_step q (n + 1) hq hq2 (by omega)
        (by simpa using ih')

end Ihara
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

end Inl_P2B_Induction
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

section Inl_P2B_M2SchurTrivial

set_option autoImplicit false

p2m_open "Matrix SpecialLinearGroup Matrix.SpecialLinearGroup Subgroup"

open scoped MatrixGroups

namespace Ihara
p2m_export "Ihara" "HasTrivialSchurMultiplier hasTrivialSchurMultiplier_of_subsingleton exists_pow_prime_pow_eq_one_of_sl2_stem"
p2m_open "Ihara"

variable (q : ℕ)

private theorem sl2coe_mul'' {R : Type*} [CommRing R] (A B : SL(2, R)) :
    ((A * B : SL(2, R)) : Matrix (Fin 2) (Fin 2) R)
      = (A : Matrix (Fin 2) (Fin 2) R) * B := rfl

abbrev unipU2 : SL(2, ZMod (q ^ 2)) := uElt (R := ZMod (q ^ 2)) 1

theorem slReduceLevel_unipU2 :
    slReduceLevel q 2 1 (by omega) (unipU2 q) = unipU (q ^ 1) := by
  ext i j
  simp only [slReduceLevel, SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply, unipU2, uElt_coe, unipU]
  fin_cases i <;> fin_cases j <;> simp

theorem congFilt_one_commute_unipU2_mem_zpowers (hq : q.Prime) (hq2 : q ≠ 2) :
    ∀ k ∈ congFilt q 2 1, unipU2 q * k = k * unipU2 q →
      k ∈ Subgroup.zpowers (unipU2 q) := by
  intro k hk hcomm
  obtain ⟨X, hX⟩ := (mem_congFilt_iff q 2).mp hk
  rw [pow_one] at hX

  have hmat : (q : ZMod (q^2)) •
      (!![(1:ZMod (q^2)),1;0,1] * X - X * !![1,1;0,1]) = 0 := by
    have hcoe := congrArg
      (fun g => ((g : SL(2, ZMod (q^2))) : Matrix (Fin 2) (Fin 2) (ZMod (q^2)))) hcomm
    simp only [sl2coe_mul'', hX,
      show ((unipU2 q : SL(2, ZMod (q^2))) : Matrix _ _ _)
        = !![(1:ZMod (q^2)),1;0,1] from rfl] at hcoe
    rw [mul_add, mul_one, add_mul, one_mul, Matrix.mul_smul, Matrix.smul_mul] at hcoe
    rw [smul_sub, sub_eq_zero]; exact add_left_cancel hcoe

  have hmat' := fun i j => congrFun (congrFun hmat i) j
  have hqX10 : (q : ZMod (q^2)) * X 1 0 = 0 := by
    have h00 := hmat' 0 0
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.zero_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.empty_val'] at h00
    linear_combination h00
  have hqXdd : (q : ZMod (q^2)) * (X 1 1 - X 0 0) = 0 := by
    have h01 := hmat' 0 1
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.zero_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.empty_val'] at h01
    linear_combination h01

  have hq2z : ((q : ZMod (q^2)) ^ 2 : ZMod (q^2)) = 0 := by
    rw [← Nat.cast_pow]; exact ZMod.natCast_self _
  have hdet := k.det_coe
  rw [hX, det_one_add_smul_fin_two, hq2z, zero_mul, add_zero] at hdet
  have hqXtr : (q : ZMod (q^2)) * (X 0 0 + X 1 1) = 0 := by
    rw [← Matrix.trace_fin_two]; linear_combination hdet

  have h2u : IsUnit (2 : ZMod (q^2)) :=
    (ZMod.isUnit_iff_coprime 2 (q^2)).mpr
      ((Nat.coprime_primes Nat.prime_two hq).mpr (by omega) |>.pow_right 2)
  have hqX00 : (q : ZMod (q^2)) * X 0 0 = 0 := by
    have h2 : 2 * ((q : ZMod (q^2)) * X 0 0) = 0 := by linear_combination hqXtr - hqXdd
    exact h2u.mul_right_eq_zero.mp h2
  have hqX11 : (q : ZMod (q^2)) * X 1 1 = 0 := by
    have h2 : 2 * ((q : ZMod (q^2)) * X 1 1) = 0 := by linear_combination hqXtr + hqXdd
    exact h2u.mul_right_eq_zero.mp h2

  haveI : NeZero (q ^ 2) := ⟨pow_ne_zero 2 hq.ne_zero⟩
  have hval : (((((q : ZMod (q^2)) * X 0 1).val : ℕ) : ZMod (q^2)))
      = (q : ZMod (q^2)) * X 0 1 := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  refine Subgroup.mem_zpowers_iff.mpr
    ⟨(((q : ZMod (q^2)) * X 0 1).val : ℤ), ?_⟩
  rw [zpow_natCast, unipU2, uElt_pow (1 : ZMod (q^2)), mul_one, hval]
  apply Matrix.SpecialLinearGroup.ext; intro i j
  rw [hX, uElt_coe, Matrix.one_fin_two]
  fin_cases i <;> fin_cases j <;> simp [hqX00, hqX10, hqX11]

theorem hasTrivialSchurMultiplier_SL2_ZMod_sq (hq : q.Prime) (hq2 : q ≠ 2)
    (IH : HasTrivialSchurMultiplier SL(2, ZMod (q ^ 1))) :
    HasTrivialSchurMultiplier SL(2, ZMod (q ^ 2)) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  intro E _ π hπ hcen hC
  have hQ : HasTrivialSchurMultiplier (SL(2, ZMod (q ^ 2)) ⧸ congFilt q 2 1) :=
    IH.of_mulEquiv (congFiltQuotientEquiv q 2 (by omega))
  have hK : congFilt q 2 1 ≤ commutator SL(2, ZMod (q ^ 2)) :=
    congFilt_top_le_commutator q 2 hq hq2 le_rfl
  have hCq : ∀ c ∈ π.ker, c ^ q = 1 :=
    ker_pow_eq_one_of_stem π hπ hcen hC (congFilt q 2 1) hK hQ
      (congFilt_commutative q 2 (a := 1) (by omega)) (hq.odd_of_ne_two (by omega))
      (fun _ hk => congFilt_pow_q_eq_one q 2 (by omega) hk)

  haveI : Fact (q ^ 1).Prime := ⟨by rw [pow_one]; exact hq⟩
  have hρu : slReduceLevel q 2 1 (by omega) (unipU2 q) = unipU (q^1) := slReduceLevel_unipU2 q
  have hidx : Nat.Coprime
      ((Subgroup.zpowers (slReduceLevel q 2 1 (by omega) (unipU2 q))).comap
        (slReduceLevel q 2 1 (by omega))).index q := by
    rw [Subgroup.index_comap_of_surjective _
        (slReduceLevel_surjective q 2 (a := 1) (by omega)),
      hρu, index_zpowers_unipU (q ^ 1),
      show (q ^ 1) ^ 2 - 1 = q ^ 2 - 1 from by rw [pow_one]]
    have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq.pos
    exact ((Nat.coprime_pow_left_iff two_pos q (q ^ 2 - 1)).mp
      ((Nat.coprime_self_sub_right h1).mpr (Nat.coprime_one_right _))).symm

  exact ker_eq_bot_of_stem_of_fibre π hπ hcen hC (congFilt q 2 1)
    (fun x hx y hy => comap_congFilt_one_commute q π hπ hcen hq hq2 x hx y hy)
    hCq (slReduceLevel q 2 1 (by omega))
    (congFilt_eq_ker_reduceLevel (q := q) (m := 2) (a := 1) (by omega)).symm
    (unipU2 q) hidx
    (congFilt_one_commute_unipU2_mem_zpowers q hq hq2)

end Ihara
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

end Inl_P2B_M2SchurTrivial
p2m_reactivate "P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.Ihara"

open scoped MatrixGroups in

theorem solution {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (n : ℕ) : Ihara.HasTrivialSchurMultiplier (SL(2, ZMod (q ^ n))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  ·
    haveI : Subsingleton (ZMod (q ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero q)
    haveI : Subsingleton (SL(2, ZMod (q ^ 0))) :=
      ⟨fun a b => Matrix.SpecialLinearGroup.ext a b fun i j => Subsingleton.elim _ _⟩
    exact Ihara.hasTrivialSchurMultiplier_of_subsingleton
  · haveI : Fact q.Prime := ⟨hq⟩
    have hA : ∀ (E : Type) [Group E] (π : E →* SL(2, ZMod q)), Function.Surjective π →
        π.ker ≤ Subgroup.center E → ∀ x ∈ π.ker, x ∈ commutator E → ∃ k : ℕ, x ^ (q ^ k) = 1 :=
      fun E _ π hπ hcen x hx hxcomm =>
        Ihara.exists_pow_prime_pow_eq_one_of_sl2_stem q hq2 π hπ hcen hx hxcomm
    have h1 : Ihara.HasTrivialSchurMultiplier (SL(2, ZMod (q ^ 1))) := by
      rw [pow_one]; exact Ihara.hasTrivialSchurMultiplier_SL2_ZMod_of_kerPowQ q hq hA
    exact Ihara.hasTrivialSchurMultiplier_SL2_ZMod_prime_pow_of q hq hq2 hA
      (Ihara.hasTrivialSchurMultiplier_SL2_ZMod_sq q hq hq2 h1) hn.ne'

end S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow
end P2MW
export P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow (solution)
