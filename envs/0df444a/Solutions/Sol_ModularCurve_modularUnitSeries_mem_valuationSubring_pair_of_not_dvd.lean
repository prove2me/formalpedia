-- Prove2me | solution 1 for ModularCurve.modularUnitSeries_mem_valuationSubring_pair_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/c68bade1-520a-5b6b-8de6-163000981a57

import Mathlib
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_modularFunctionFieldFull_algHom_ext
import Theorems.Thm_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime
import Theorems.Thm_ModularCurve_coe_frickeInvolutionFull_modularUnitSeries
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_modularUnitSeries_mem_valuationSubring_pair_of_not_dvd
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

open ModularCurve IntermediateField AlgebraicCurve

namespace LigozatUnitEngine

def deltaInt : LaurentSeries ℤ :=
  HahnSeries.ofPowerSeries ℤ ℤ (PowerSeries.X * dedekindEtaUnit)

def deltaInvInt : LaurentSeries ℤ :=
  HahnSeries.single (-1) 1 * HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv

theorem deltaInt_eq : deltaInt = HahnSeries.single 1 1 * HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnit := by
  rw [deltaInt, map_mul, HahnSeries.ofPowerSeries_X]

theorem deltaInt_mul_deltaInvInt : deltaInt * deltaInvInt = 1 := by
  rw [deltaInt_eq, deltaInvInt, mul_mul_mul_comm, HahnSeries.single_mul_single, ← map_mul,
    dedekindEtaUnit_mul_inv, map_one, mul_one]
  simp

variable (p : ℕ) [Fact p.Prime]

def unitInt : LaurentSeries ℤ := deltaInt * qExpand ℤ p deltaInvInt

def unitInvInt : LaurentSeries ℤ := deltaInvInt * qExpand ℤ p deltaInt

theorem unitInt_mul_unitInvInt : unitInt p * unitInvInt p = 1 := by
  rw [unitInt, unitInvInt, mul_mul_mul_comm, deltaInt_mul_deltaInvInt, ← map_mul,
    mul_comm deltaInvInt, deltaInt_mul_deltaInvInt, map_one, mul_one]

section CoeffMap

variable {K : Type*} [CommRing K]

theorem coeffMap_deltaInt (f : ℤ →+* K) :
    coeffMap f deltaInt =
      HahnSeries.ofPowerSeries ℤ K (PowerSeries.map f (PowerSeries.X * dedekindEtaUnit)) := by
  rw [deltaInt, coeffMap_ofPowerSeries]

theorem coeffMap_deltaInt_mul_deltaInvInt (f : ℤ →+* K) :
    coeffMap f deltaInt * coeffMap f deltaInvInt = 1 := by
  rw [← map_mul, deltaInt_mul_deltaInvInt, map_one]

theorem coeffMap_unitInt (f : ℤ →+* K) :
    coeffMap f (unitInt p) = coeffMap f deltaInt * qExpand K p (coeffMap f deltaInvInt) := by
  rw [unitInt, map_mul, ModularCurve.coeffMap_qExpand]

theorem coeffMap_unitInvInt (f : ℤ →+* K) :
    coeffMap f (unitInvInt p) = coeffMap f deltaInvInt * qExpand K p (coeffMap f deltaInt) := by
  rw [unitInvInt, map_mul, ModularCurve.coeffMap_qExpand]

theorem coeffMap_unitInt_mul_unitInvInt (f : ℤ →+* K) :
    coeffMap f (unitInt p) * coeffMap f (unitInvInt p) = 1 := by
  rw [← map_mul, unitInt_mul_unitInvInt, map_one]

theorem isUnit_coeffMap_unitInt (f : ℤ →+* K) : IsUnit (coeffMap f (unitInt p)) :=
  IsUnit.of_mul_eq_one _ (coeffMap_unitInt_mul_unitInvInt p f)

theorem isUnit_coeffMap_unitInvInt (f : ℤ →+* K) : IsUnit (coeffMap f (unitInvInt p)) :=
  IsUnit.of_mul_eq_one_right _ (coeffMap_unitInt_mul_unitInvInt p f)

theorem coeffMap_unitInt_ne_zero [Nontrivial K] (f : ℤ →+* K) : coeffMap f (unitInt p) ≠ 0 :=
  (isUnit_coeffMap_unitInt p f).ne_zero

theorem coeffMap_unitInvInt_ne_zero [Nontrivial K] (f : ℤ →+* K) : coeffMap f (unitInvInt p) ≠ 0 :=
  (isUnit_coeffMap_unitInvInt p f).ne_zero

end CoeffMap

theorem coeffMap_rat_deltaInt : coeffMap (Int.castRingHom ℚ) deltaInt = deltaSeries := by
  rw [deltaInt_eq, map_mul, coeffMap_single, map_one, coeffMap_ofPowerSeries]
  rfl

theorem coeffMap_rat_deltaInvInt : coeffMap (Int.castRingHom ℚ) deltaInvInt = deltaSeries⁻¹ := by
  refine (inv_eq_of_mul_eq_one_right ?_).symm
  rw [← coeffMap_rat_deltaInt, coeffMap_deltaInt_mul_deltaInvInt]

theorem coeffMap_rat_unitInt : coeffMap (Int.castRingHom ℚ) (unitInt p) = modularUnitSeries p := by
  rw [coeffMap_unitInt, coeffMap_rat_deltaInt, coeffMap_rat_deltaInvInt, map_inv₀]
  rfl

theorem coeffMap_rat_unitInvInt :
    coeffMap (Int.castRingHom ℚ) (unitInvInt p) = (modularUnitSeries p)⁻¹ := by
  refine (inv_eq_of_mul_eq_one_right ?_).symm
  rw [← coeffMap_rat_unitInt, coeffMap_unitInt_mul_unitInvInt]

end LigozatUnitEngine

namespace LigozatUnitAL

variable (N p : ℕ) [NeZero N] [Fact p.Prime]

def incl : modularFunctionFieldFull p →+* modularFunctionFieldFull (N * p) where
  toFun x := ⟨x.1, full_degeneracy_le (dvd_mul_left p N) x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem incl_apply (x : modularFunctionFieldFull p) :
    incl N p x = ⟨x.1, full_degeneracy_le (dvd_mul_left p N) x.2⟩ := rfl

theorem coe_incl (x : modularFunctionFieldFull p) :
    ((incl N p x : modularFunctionFieldFull (N * p)) : LaurentSeries ℚ) = (x : LaurentSeries ℚ) := by
  rw [incl_apply]

theorem atkinLehner_comp_incl (hpN : ¬ p ∣ N) :
    (((atkinLehnerInvolutionFull N p : _ →+* _).comp (incl N p)).toRatAlgHom :
        modularFunctionFieldFull p →ₐ[ℚ] modularFunctionFieldFull (N * p))
      = ((incl N p).comp (frickeInvolutionFull p : _ →+* _)).toRatAlgHom := by
  have hσ : IsAtkinLehnerAutFull N p (atkinLehnerInvolutionFull N p) :=
    isAtkinLehnerAutFull_atkinLehnerInvolutionFull N p
      (ModularCurve.exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N p Fact.out hpN)
  have hτ : IsFrickeAutFull p (frickeInvolutionFull p) :=
    ModularCurve.isFrickeAutFull_frickeInvolutionFull_prime p
  obtain ⟨h1, h2⟩ := hσ 1 inferInstance (one_dvd N)
  have hτ1 := hτ 1 p (one_mul p) inferInstance inferInstance
  have hτ2 := hτ p 1 (mul_one p) inferInstance inferInstance
  refine ModularCurve.modularFunctionFieldFull_algHom_ext fun d hd0 hd => ?_
  rw [RingHom.toRatAlgHom_apply, RingHom.toRatAlgHom_apply, RingHom.comp_apply, RingHom.comp_apply,
    RingHom.coe_coe, RingHom.coe_coe]
  apply Subtype.ext
  rw [coe_incl]
  rcases (Nat.dvd_prime Fact.out).mp hd with rfl | rfl
  ·
    have hel : incl N p (⟨qExpand ℚ 1 jq, jqd_mem_full p hd⟩ : modularFunctionFieldFull p) =
        ⟨qExpand ℚ 1 jq, jqd_mem_full (N * p) (Dvd.dvd.mul_right (one_dvd N) p)⟩ := by
      rw [incl_apply]
    rw [hel, h1, hτ1]
    exact qExpand_congr (one_mul p) jq
  ·
    have hel : incl N d (⟨qExpand ℚ d jq, jqd_mem_full d hd⟩ : modularFunctionFieldFull d) =
        ⟨qExpand ℚ (1 * d) jq, jqd_mem_full (N * d) (Nat.mul_dvd_mul_right (one_dvd N) d)⟩ := by
      rw [incl_apply]; exact Subtype.ext (qExpand_congr (one_mul d).symm jq)
    rw [hel, h2, hτ2]

theorem coe_atkinLehnerInvolutionFull_modularUnitSeries (hpN : ¬ p ∣ N)
    (hmem : modularUnitSeries p ∈ modularFunctionFieldFull (N * p)) :
    ((atkinLehnerInvolutionFull N p ⟨modularUnitSeries p, hmem⟩ :
        modularFunctionFieldFull (N * p)) : LaurentSeries ℚ) =
      (p : ℚ) ^ 12 • (modularUnitSeries p)⁻¹ := by
  have hu : modularUnitSeries p ∈ modularFunctionFieldFull p :=
    ModularCurve.modularUnitSeries_mem_modularFunctionFieldFull p
  have key := AlgHom.congr_fun (atkinLehner_comp_incl N p hpN) ⟨modularUnitSeries p, hu⟩
  rw [RingHom.toRatAlgHom_apply, RingHom.toRatAlgHom_apply, RingHom.comp_apply, RingHom.comp_apply,
    RingHom.coe_coe, RingHom.coe_coe] at key
  have hel : incl N p (⟨modularUnitSeries p, hu⟩ : modularFunctionFieldFull p) =
      (⟨modularUnitSeries p, hmem⟩ : modularFunctionFieldFull (N * p)) := by rw [incl_apply]
  rw [hel] at key
  rw [key, coe_incl, ModularCurve.coe_frickeInvolutionFull_modularUnitSeries p hu]

theorem atkinLehnerInvolutionFull_modularUnitSeries (hpN : ¬ p ∣ N)
    (hmem : modularUnitSeries p ∈ modularFunctionFieldFull (N * p)) :
    atkinLehnerInvolutionFull N p ⟨modularUnitSeries p, hmem⟩ =
      ((p : ℕ) : modularFunctionFieldFull (N * p)) ^ 12 *
        (⟨modularUnitSeries p, hmem⟩ : modularFunctionFieldFull (N * p))⁻¹ := by
  apply Subtype.ext
  rw [coe_atkinLehnerInvolutionFull_modularUnitSeries N p hpN hmem, MulMemClass.coe_mul,
    SubmonoidClass.coe_pow]
  rw [← HahnSeries.C_mul_eq_smul, map_pow, map_natCast]
  norm_cast

end LigozatUnitAL

namespace LigozatUnitQ

open LigozatUnitEngine LigozatUnitAL

variable (N p : ℕ) [NeZero N] [Fact p.Prime]

local notation "F" => modularFunctionFieldFull (N * p)

theorem main (hpN : ¬ p ∣ N) (hmem : modularUnitSeries p ∈ modularFunctionFieldFull (N * p))
    (W₀ W₁ : ValuationSubring F)
    (hW₀ : ∀ f : F, f ∈ W₀ ↔
      ∃ x y : LaurentSeries ℤ, coeffMap (Int.castRingHom (ZMod p)) y ≠ 0 ∧
        (f : LaurentSeries ℚ) * coeffMap (Int.castRingHom ℚ) y = coeffMap (Int.castRingHom ℚ) x)
    (hW₁ : ∀ f : F, f ∈ W₁ ↔ atkinLehnerInvolutionFull N p f ∈ W₀) :
    (∃ x : LaurentSeries ℤ, coeffMap (Int.castRingHom (ZMod p)) x ≠ 0 ∧
        modularUnitSeries p = coeffMap (Int.castRingHom ℚ) x) ∧
    (∃ x : LaurentSeries ℤ, coeffMap (Int.castRingHom (ZMod p)) x ≠ 0 ∧
        (modularUnitSeries p)⁻¹ = coeffMap (Int.castRingHom ℚ) x) ∧
    ((⟨modularUnitSeries p, hmem⟩ : F) ∈ W₀ ∧ (⟨modularUnitSeries p, hmem⟩ : F)⁻¹ ∈ W₀) ∧
    ((⟨modularUnitSeries p, hmem⟩ : F) * (((p : ℕ) : F) ^ 12)⁻¹ ∈ W₁ ∧
      ((⟨modularUnitSeries p, hmem⟩ : F) * (((p : ℕ) : F) ^ 12)⁻¹)⁻¹ ∈ W₁) := by
  set uF : F := ⟨modularUnitSeries p, hmem⟩ with huF_def
  have hx : coeffMap (Int.castRingHom (ZMod p)) (unitInt p) ≠ 0 := coeffMap_unitInt_ne_zero p _
  have hx' : coeffMap (Int.castRingHom (ZMod p)) (unitInvInt p) ≠ 0 := coeffMap_unitInvInt_ne_zero p _
  have hone : coeffMap (Int.castRingHom (ZMod p)) 1 ≠ 0 := by rw [map_one]; exact one_ne_zero
  have hu₀ : uF ∈ W₀ := (hW₀ uF).mpr ⟨unitInt p, 1, hone, by
    rw [map_one, mul_one, coeffMap_rat_unitInt]⟩
  have hu₀inv : uF⁻¹ ∈ W₀ := (hW₀ _).mpr ⟨unitInvInt p, 1, hone, by
    rw [map_one, mul_one, coeffMap_rat_unitInvInt, IntermediateField.coe_inv]⟩
  have hp0 : ((p : ℕ) : F) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hP0 : ((p : ℕ) : F) ^ 12 ≠ 0 := pow_ne_zero _ hp0
  have hwu : atkinLehnerInvolutionFull N p uF = ((p : ℕ) : F) ^ 12 * uF⁻¹ :=
    atkinLehnerInvolutionFull_modularUnitSeries N p hpN hmem
  have hwP : atkinLehnerInvolutionFull N p (((p : ℕ) : F) ^ 12) = ((p : ℕ) : F) ^ 12 := by
    rw [map_pow, map_natCast]
  have hc1 : uF * (((p : ℕ) : F) ^ 12)⁻¹ ∈ W₁ := by
    rw [hW₁, map_mul, map_inv₀, hwP, hwu, mul_assoc, mul_comm uF⁻¹, ← mul_assoc,
      mul_inv_cancel₀ hP0, one_mul]
    exact hu₀inv
  have hc2 : (uF * (((p : ℕ) : F) ^ 12)⁻¹)⁻¹ ∈ W₁ := by
    rw [mul_inv, inv_inv, hW₁, map_mul, map_inv₀, hwP, hwu, mul_inv, inv_inv, mul_assoc,
      mul_comm uF, ← mul_assoc, inv_mul_cancel₀ hP0, one_mul]
    exact hu₀
  exact ⟨⟨unitInt p, hx, (coeffMap_rat_unitInt p).symm⟩,
    ⟨unitInvInt p, hx', (coeffMap_rat_unitInvInt p).symm⟩, ⟨hu₀, hu₀inv⟩, hc1, hc2⟩

end LigozatUnitQ

end

theorem solution
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N)
    (hmem : ModularCurve.modularUnitSeries p ∈ ModularCurve.modularFunctionFieldFull (N * p))
    (W₀ W₁ : ValuationSubring ↥(ModularCurve.modularFunctionFieldFull (N * p)))

    (hW₀ : ∀ f : ↥(ModularCurve.modularFunctionFieldFull (N * p)), f ∈ W₀ ↔
      ∃ x y : LaurentSeries ℤ, ModularCurve.coeffMap (Int.castRingHom (ZMod p)) y ≠ 0 ∧
        (f : LaurentSeries ℚ) * ModularCurve.coeffMap (Int.castRingHom ℚ) y
          = ModularCurve.coeffMap (Int.castRingHom ℚ) x)

    (hW₁ : ∀ f : ↥(ModularCurve.modularFunctionFieldFull (N * p)), f ∈ W₁ ↔
      ModularCurve.atkinLehnerInvolutionFull N p f ∈ W₀) :

    (∃ x : LaurentSeries ℤ, ModularCurve.coeffMap (Int.castRingHom (ZMod p)) x ≠ 0 ∧
        ModularCurve.modularUnitSeries p = ModularCurve.coeffMap (Int.castRingHom ℚ) x) ∧
    (∃ x : LaurentSeries ℤ, ModularCurve.coeffMap (Int.castRingHom (ZMod p)) x ≠ 0 ∧
        (ModularCurve.modularUnitSeries p)⁻¹ = ModularCurve.coeffMap (Int.castRingHom ℚ) x) ∧

    ((⟨ModularCurve.modularUnitSeries p, hmem⟩ : ↥(ModularCurve.modularFunctionFieldFull (N * p))) ∈ W₀ ∧
      (⟨ModularCurve.modularUnitSeries p, hmem⟩ : ↥(ModularCurve.modularFunctionFieldFull (N * p)))⁻¹ ∈ W₀) ∧

    ((⟨ModularCurve.modularUnitSeries p, hmem⟩ : ↥(ModularCurve.modularFunctionFieldFull (N * p))) *
          (((p : ℕ) : ↥(ModularCurve.modularFunctionFieldFull (N * p))) ^ 12)⁻¹ ∈ W₁ ∧
      ((⟨ModularCurve.modularUnitSeries p, hmem⟩ : ↥(ModularCurve.modularFunctionFieldFull (N * p))) *
          (((p : ℕ) : ↥(ModularCurve.modularFunctionFieldFull (N * p))) ^ 12)⁻¹)⁻¹ ∈ W₁) :=
  LigozatUnitQ.main N p hpN hmem W₀ W₁ hW₀ hW₁

end S_ModularCurve_modularUnitSeries_mem_valuationSubring_pair_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_modularUnitSeries_mem_valuationSubring_pair_of_not_dvd (solution)
