-- Prove2me | solution 1 for GroundTheory.LocalField.exists_smul_one_mem_spanZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:37:28.976257+00:00
-- url     : https://prove2.me/submissions/a18299ff-3a24-465c-a003-5826d3a5cef8

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionPrime
import Theorems.Thm_GroundTheory_LocalField_brauerFun_mem_spanA
import Theorems.Thm_GroundTheory_LocalField_not_dvd_brauerFun
import Theorems.Thm_GroundTheory_LocalField_IsElementaryAt_mono
import Theorems.Thm_GroundTheory_LocalField_IsIrrCharacter_isCharacter
import Theorems.Thm_GroundTheory_LocalField_isCharacter_one
import Theorems.Thm_GroundTheory_LocalField_isClassFun_of_mem_spanA
import Theorems.Thm_GroundTheory_LocalField_isElementaryAt_zpowers
import Theorems.Thm_GroundTheory_LocalField_mem_irrChars
import Theorems.Thm_GroundTheory_LocalField_mem_spanA_of_dvd
import Theorems.Thm_GroundTheory_LocalField_mem_spanZ_of_mem_spanA
import Theorems.Thm_GroundTheory_LocalField_pow_mem_spanA


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
open scoped Classical
universe u
variable {G : Type u} [Group G]
variable [Fintype G] (p : ℕ) [hp : Fact p.Prime] (x : G)
variable {p x}
variable {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Nat.card G))
  (hmono : ∀ K : Subgroup G, IsElementaryAt p K → ∀ χ : K → ℂ, IsIrrCharacter χ →
    ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ)
include hζ hmono
namespace GroundTheory.LocalField
theorem _root_.solution :
    ∃ m : ℕ, ¬ p ∣ m ∧ ((m : ℤ) • (1 : G → ℂ)) ∈ spanZ (IsElementaryAt p) := by
  have hE : ∀ K L : Subgroup G, IsElementaryAt p K → L ≤ K → IsElementaryAt p L :=
    fun K L hK hLK ↦ hK.mono hLK
  have hcyc : ∀ s : G, IsElementaryAt p (Subgroup.zpowers s) := fun s ↦ isElementaryAt_zpowers hp.out s
  set n := Nat.card G
  set e := n.factorization p
  set q := p ^ e
  set m := n / q
  have hn : q * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
  set M := Nat.totient q
  have hq0 : 0 < q := pow_pos hp.out.pos e
  have hM : M ≠ 0 := (Nat.totient_pos.mpr hq0).ne'
  have : NeZero q := ⟨hq0.ne'⟩
  set f : G → ℂ := brauerFun p
  have hfA : f ∈ spanA (G := G) (IsElementaryAt p) ζ := brauerFun_mem_spanA hζ hmono
  have hval : ∀ s, ∃ j : ℤ, (f ^ M - 1) s = (q : ℂ) * j := by
    intro s
    obtain ⟨k, hk, hpk⟩ := not_dvd_brauerFun hζ hmono s
    have hcop : Nat.Coprime k.natAbs q := Nat.Coprime.pow_right e
      ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr fun h ↦ hpk (Int.natCast_dvd.mpr h)).symm
    have hunit : IsUnit (k : ZMod q) := by
      rcases Int.natAbs_eq k with h | h
      · rw [h, Int.cast_natCast]
        exact (ZMod.isUnit_iff_coprime _ _).mpr hcop
      · rw [h, Int.cast_neg, Int.cast_natCast]
        exact ((ZMod.isUnit_iff_coprime _ _).mpr hcop).neg
    have hpow : ((k ^ M - 1 : ℤ) : ZMod q) = 0 := by
      have h2 : (k : ZMod q) ^ M = 1 := by
        have := congrArg Units.val (ZMod.pow_totient hunit.unit)
        rwa [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one] at this
      push_cast
      rw [h2, sub_self]
    obtain ⟨j, hj⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hpow
    refine ⟨j, ?_⟩
    simp only [Pi.sub_apply, Pi.pow_apply, Pi.one_apply]
    rw [show f s = (k : ℂ) from hk, show ((k : ℂ) ^ M - 1) = ((k ^ M - 1 : ℤ) : ℂ) by push_cast; ring, hj]
    push_cast
    ring
  have hcl : IsClassFun f := isClassFun_of_mem_spanA hfA
  have hF1 : ((m : ℤ) • (f ^ M - 1)) ∈ spanA (G := G) (IsElementaryAt p) ζ := by
    apply mem_spanA_of_dvd hE hmono hcyc hζ
    · intro g h
      simp [hcl g h]
    · intro g
      obtain ⟨j, hj⟩ := hval g
      refine ⟨j, ?_⟩
      have hn' : (Nat.card G : ℂ) = q * m := by exact_mod_cast hn.symm
      rw [Pi.smul_apply, hj, zsmul_eq_mul, hn']
      push_cast
      ring
  have hfM := pow_mem_spanA hE hmono hfA hM
  have h1 : ((m : ℤ) • (1 : G → ℂ)) = (m : ℤ) • f ^ M - (m : ℤ) • (f ^ M - 1) := by
    rw [smul_sub]
    abel
  have hA1 : ((m : ℤ) • (1 : G → ℂ)) ∈ spanA (G := G) (IsElementaryAt p) ζ := by
    rw [h1]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hfM) hF1
  refine ⟨m, Nat.not_dvd_ordCompl hp.out Nat.card_pos.ne', ?_⟩
  apply mem_spanZ_of_mem_spanA (hζ.isIntegral Nat.card_pos) hA1
  intro ψ hψ
  obtain ⟨j, hj⟩ := isCharacter_one.exists_nat_charInner (mem_irrChars.mp hψ).isCharacter
  refine ⟨m * j, ?_⟩
  rw [map_zsmul, LinearMap.smul_apply, hj, zsmul_eq_mul]
  push_cast
  ring
end GroundTheory.LocalField
