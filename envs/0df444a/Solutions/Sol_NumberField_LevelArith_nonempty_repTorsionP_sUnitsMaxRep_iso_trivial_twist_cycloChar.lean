-- Prove2me | solution 1 for NumberField.LevelArith.nonempty_repTorsionP_sUnitsMaxRep_iso_trivial_twist_cycloChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/bbb92c4f-a96c-500d-896f-2089dfccb51e

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_NumberField_SUnitsMax
import Theorems.Thm_IntermediateField_isUnramifiedOutside_sup_adjoin_of_pow_eq
import Theorems.Thm_NumberField_LevelArith_sUnitsMaxStable_eq_sUnitsMax
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_nonempty_repTorsionP_sUnitsMaxRep_iso_trivial_twist_cycloChar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith"
open scoped Classical NumberField NumberField.LevelArith TensorProduct Pointwise

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain"
open scoped Classical NumberField NumberField.LevelArith

open scoped TensorProduct Pointwise

local instance CycBaseMu.isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ

namespace CycBaseMu

variable (p : ℕ) [Fact p.Prime]

lemma exists_isPrimitiveRoot : ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ p := by
  haveI : NeZero ((p : ℕ) : AlgebraicClosure ℚ) := ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic p (AlgebraicClosure ℚ)) (by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr (Fact.out : p.Prime).pos).ne')
  exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζ⟩

variable (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
include hζ

lemma apply_eq_pow_cycloChar (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    γ ζ = ζ ^ ((cycloChar p γ : ZMod p)).val := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (Fact.out : p.Prime).ne_zero
  have ht : Units.mk0 ζ hζ0 ∈ rootsOfUnity p (AlgebraicClosure ℚ) := by
    rw [mem_rootsOfUnity]; apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]; exact hζ.pow_eq_one
  have h := modularCyclotomicCharacter.spec (AlgebraicClosure ℚ) (card_rootsOfUnity_eq_self p)
    (γ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) ht
  rw [Units.val_mk0] at h
  exact h

end CycBaseMu

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    Nonempty (repTorsionP p (sUnitsMaxRep S L) ≅
      (Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype)) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := CycBaseMu.exists_isPrimitiveRoot p
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero

  have hlev : (⊥ ⊔ IntermediateField.adjoin ℚ {ζ}).IsUnramifiedOutside S :=
    IntermediateField.isUnramifiedOutside_sup_adjoin_of_pow_eq S (pPrime p) hpS ⊥ (IntermediateField.isUnramifiedOutside_bot S)
      1 (one_mem _) (fun q _ A _ => ⟨one_mem A, by rw [inv_one]; exact one_mem A⟩) ζ hζ.pow_eq_one
  have hζunit : ∀ A : ValuationSubring (AlgebraicClosure ℚ), ζ ∈ A ∧ ζ⁻¹ ∈ A := by
    intro A
    have hv : A.valuation ζ = 1 := by
      have h := congrArg A.valuation hζ.pow_eq_one
      rw [map_pow, map_one] at h
      exact (pow_eq_one_iff_left hp.ne_zero).mp h
    refine ⟨(A.valuation_le_one_iff _).mp hv.le, (A.valuation_le_one_iff _).mp ?_⟩
    rw [map_inv₀, hv, inv_one]
  have hζmem : Units.mk0 ζ hζ0 ∈ sUnitsMaxStable S L := by
    rw [sUnitsMaxStable_eq_sUnitsMax]
    refine ⟨⟨⊥ ⊔ IntermediateField.adjoin ℚ {ζ}, hlev, ?_⟩, fun q hq A hA => ?_⟩
    · exact (le_sup_right : IntermediateField.adjoin ℚ {ζ} ≤ _) (IntermediateField.mem_adjoin_simple_self ℚ ζ)
    · refine ⟨(hζunit A).1, ?_⟩
      rw [Units.val_inv_eq_inv_val, Units.val_mk0]; exact (hζunit A).2

  let eζ : sUnitsMaxRep S L := ⟨Additive.ofMul (Units.mk0 ζ hζ0), hζmem⟩
  have hval : ∀ n : ℕ, ((n • eζ : sUnitsMaxRep S L).1 : Additive (AlgebraicClosure ℚ)ˣ) = Additive.ofMul (Units.mk0 ζ hζ0 ^ n) := by
    intro n
    show n • Additive.ofMul (Units.mk0 ζ hζ0) = _
    rw [ofMul_pow]
  have hpe : (p : ℤ) • eζ = 0 := by
    rw [natCast_zsmul]
    apply Subtype.ext
    rw [hval]
    show Additive.ofMul (Units.mk0 ζ hζ0 ^ p) = Additive.ofMul 1
    congr 1
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]; exact hζ.pow_eq_one
  let tζ : ↥(Submodule.torsionBy ℤ (sUnitsMaxRep S L) (p : ℤ)) := ⟨eζ, (Submodule.mem_torsionBy_iff _ _).mpr hpe⟩

  have htval : ∀ n : ℕ, sUnitsMaxRep.val S L ((n • tζ : ↥(Submodule.torsionBy ℤ (sUnitsMaxRep S L) (p : ℤ))) : sUnitsMaxRep S L) =
      Units.mk0 ζ hζ0 ^ n := by
    intro n
    show Additive.toMul (((n • tζ : ↥(Submodule.torsionBy ℤ (sUnitsMaxRep S L) (p : ℤ))) : sUnitsMaxRep S L).1) = _
    rw [show (((n • tζ : ↥(Submodule.torsionBy ℤ (sUnitsMaxRep S L) (p : ℤ))) : sUnitsMaxRep S L)) = n • eζ from rfl, hval]
    rfl

  let φ : ZMod p →ₗ[ZMod p] ↥(Submodule.torsionBy ℤ (sUnitsMaxRep S L) (p : ℤ)) := LinearMap.toSpanSingleton (ZMod p) _ tζ
  have hφ : ∀ c : ZMod p, φ c = c.val • tζ := by
    intro c
    show c • tζ = c.val • tζ
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    exact Nat.cast_smul_eq_nsmul (ZMod p) c.val tζ

  have hsurj : Function.Surjective φ := by
    intro t
    have htp : ((sUnitsMaxRep.val S L (t : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ p = 1 := by
      have h := (Submodule.mem_torsionBy_iff (p : ℤ) (t : sUnitsMaxRep S L)).mp t.2
      rw [natCast_zsmul] at h
      have h2 := congrArg (fun e : sUnitsMaxRep S L => ((Additive.toMul e.1 : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) h
      change (((sUnitsMaxRep.val S L (t : sUnitsMaxRep S L)) ^ p : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
        ((1 : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) at h2
      rw [Units.val_pow_eq_pow_val, Units.val_one] at h2
      exact h2
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one htp
    refine ⟨(i : ZMod p), ?_⟩
    rw [hφ]
    apply Subtype.ext; apply Subtype.ext
    show (((((i : ZMod p).val • tζ : ↥(Submodule.torsionBy ℤ (sUnitsMaxRep S L) (p : ℤ))) : sUnitsMaxRep S L)).1) = (t : sUnitsMaxRep S L).1
    apply Additive.toMul.injective
    show sUnitsMaxRep.val S L _ = sUnitsMaxRep.val S L _
    rw [htval]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, ← hi, ZMod.val_natCast]
    conv_rhs => rw [← Nat.div_add_mod i p, pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    rw [hφ] at hc
    have h1 : ζ ^ c.val = 1 := by
      have h2 := congrArg (fun t : ↥(Submodule.torsionBy ℤ (sUnitsMaxRep S L) (p : ℤ)) =>
        ((sUnitsMaxRep.val S L (t : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) hc
      simp only at h2
      rw [htval, Units.val_pow_eq_pow_val, Units.val_mk0] at h2
      exact h2
    have h3 : p ∣ c.val := (hζ.pow_eq_one_iff_dvd c.val).mp h1
    have h4 : c.val = 0 := Nat.eq_zero_of_dvd_of_lt h3 (ZMod.val_lt c)
    exact (ZMod.val_eq_zero c).mp h4
  have he : ∀ g : ↥L.fixingSubgroup,
      (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩ : ZMod p →ₗ[ZMod p] ↥(Submodule.torsionBy ℤ (sUnitsMaxRep S L) (p : ℤ))) ∘ₗ
        ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype)).ρ g =
      (repTorsionP p (sUnitsMaxRep S L)).ρ g ∘ₗ
        (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩ : ZMod p →ₗ[ZMod p] ↥(Submodule.torsionBy ℤ (sUnitsMaxRep S L) (p : ℤ))) := by
    intro g
    apply LinearMap.ext_ring
    show φ (((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype)).ρ g 1) =
      (repTorsionP p (sUnitsMaxRep S L)).ρ g (φ 1)
    have lhs : ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype)).ρ g 1 =
        (cycloChar p (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : ZMod p) := by
      show ((((cycloChar p).comp L.fixingSubgroup.subtype) g : (ZMod p)ˣ) : ZMod p) * 1 = _
      rw [mul_one]; rfl
    rw [lhs, hφ, hφ, ZMod.val_one, one_smul]
    have key : sUnitsMaxRep.val S L (((cycloChar p (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : ZMod p).val • tζ :
        ↥(Submodule.torsionBy ℤ (sUnitsMaxRep S L) (p : ℤ))) : sUnitsMaxRep S L) =
        sUnitsMaxRep.val S L (((repTorsionP p (sUnitsMaxRep S L)).ρ g tζ :
          ↥(Submodule.torsionBy ℤ (sUnitsMaxRep S L) (p : ℤ))) : sUnitsMaxRep S L) := by
      have rhs : sUnitsMaxRep.val S L (((repTorsionP p (sUnitsMaxRep S L)).ρ g tζ :
          ↥(Submodule.torsionBy ℤ (sUnitsMaxRep S L) (p : ℤ))) : sUnitsMaxRep S L) =
          (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • Units.mk0 ζ hζ0 := rfl
      rw [htval, rhs]
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0]
      exact (CycBaseMu.apply_eq_pow_cycloChar p ζ hζ _).symm
    exact Subtype.ext (Subtype.ext (Additive.toMul.injective key))
  exact ⟨(Rep.mkIso (Representation.Equiv.mk (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩) he)).symm⟩

end S_NumberField_LevelArith_nonempty_repTorsionP_sUnitsMaxRep_iso_trivial_twist_cycloChar
end P2MW
export P2MW.S_NumberField_LevelArith_nonempty_repTorsionP_sUnitsMaxRep_iso_trivial_twist_cycloChar (solution)
